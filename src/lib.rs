//! Polymorphic data store (collection)

// TODO: no_std?

use std::any::TypeId;
use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;
use std::mem::size_of;
use std::ops::Deref;
use std::slice;

/// The polymorphic data store
///
/// Internally this uses a `HashMap` with boxed values, thus performance is
/// much like that of `HashMap`.
// TODO: this is a map... rename?
#[derive(Debug)]
// TODO: faster hash
// FIXME: we cannot Drop values!
pub struct Store<K>(HashMap<K, (TypeId, Box<[u8]>)>);

impl<K> Default for Store<K> {
    fn default() -> Self {
        Store::new()
    }
}

/// Typed key used to access elements
pub struct TaggedKey<K, V>(pub K, PhantomData<V>);
impl<K, V> TaggedKey<K, V> {
    /// Construct from a `key`
    pub fn new(key: K) -> Self {
        TaggedKey(key, Default::default())
    }
}
impl<K, V> Deref for TaggedKey<K, V> {
    type Target = K;
    fn deref(&self) -> &K {
        &self.0
    }
}

impl<K> Store<K> {
    /// Construct a new store
    pub fn new() -> Self {
        Store(HashMap::new())
    }

    // TODO: other ctors: with_capacity, with_hasher, ..., capacity, reserve, shrink_to_fit?
    // TODO: iterators: key tags
    // TODO: access to the hasher?
    // TODO: entry API

    /// Returns the number of elements in the store
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns true if the store contains no elements
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Clears the store, removing all elements
    pub fn clear(&mut self) {
        self.0.clear();
    }
}

impl<K: Eq + Hash> Store<K> {
    /// Checks whether a value matching the specified `key` exists
    pub fn contains_key(&self, key: &K) -> bool {
        self.0.contains_key(key)
    }

    /// Returns a reference to the value corresponding to the key
    ///
    /// The value's type is inferred from the [`TaggedKey`].
    ///
    /// Returns `None` if no element matches `tag` or if the type `V` does not match the element.
    pub fn get<V: 'static>(&self, key: &TaggedKey<K, V>) -> Option<&V> {
        self.get_typed::<V>(key)
    }

    /// Returns a reference to the value corresponding to the key
    ///
    /// The value's type must be specified explicitly.
    ///
    /// Returns `None` if no element matches `tag` or if the type `V` does not match the element.
    pub fn get_typed<V: 'static>(&self, key: &K) -> Option<&V> {
        if let Some(v) = self.0.get(key) {
            if v.0 == TypeId::of::<V>() {
                let slice: &[u8] = &*v.1;
                debug_assert_eq!(slice.len(), size_of::<V>());
                let p = slice.as_ptr() as *const u8 as *const V;
                return Some(unsafe { &*p });
            }
        }
        None
    }

    /// Returns a mutable reference to the value corresponding to the key
    pub fn get_mut<V: 'static>(&mut self, key: &TaggedKey<K, V>) -> Option<&mut V> {
        self.get_typed_mut::<V>(key)
    }

    /// Returns a mutable reference to the value corresponding to the key
    ///
    /// Returns `None` if no element matches `key` or if the type `V` does not match the element.
    pub fn get_typed_mut<V: 'static>(&mut self, key: &K) -> Option<&mut V> {
        if let Some(v) = self.0.get_mut(key) {
            if v.0 == TypeId::of::<V>() {
                let slice: &mut [u8] = &mut *v.1;
                debug_assert_eq!(slice.len(), size_of::<V>());
                let p = slice.as_mut_ptr() as *mut u8 as *mut V;
                return Some(unsafe { &mut *p });
            }
        }
        None
    }

    /// Inserts a key-value pair into the store
    ///
    /// Returns the corresponding [`TaggedKey`] for convenience.
    ///
    /// Unlike [`HashMap`] this does not return any displaced old value since
    /// the type of any such value is unknown.
    pub fn insert<V: 'static>(&mut self, key: K, value: V) -> TaggedKey<K, V>
    where
        K: Clone,
    {
        let boxed = Box::new(value);
        let type_erased = unsafe {
            let raw = Box::into_raw(boxed) as *mut u8;
            let slice = slice::from_raw_parts_mut(raw, size_of::<V>());
            Box::<[u8]>::from_raw(slice)
        };
        self.0.insert(key.clone(), (TypeId::of::<V>(), type_erased));
        TaggedKey::new(key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_and_access() {
        let mut store = Store::new();

        let k1 = store.insert(1, "A static str");
        if let Some(v) = store.get_mut(&k1) {
            *v = "another str";
        }
        assert_eq!(store.get(&k1), Some(&"another str"));

        let k2 = store.insert(2, "A String".to_string());
        assert_eq!(store.get(&k2), Some(&"A String".to_string()));

        assert!(store.contains_key(&k1));
        assert!(store.contains_key(&1));
        assert!(!store.contains_key(&3));
    }

    #[test]
    fn zero_sized() {
        let mut store = Store::new();
        let k = store.insert(1, ());
        assert_eq!(store.get(&k), Some(&()));
    }
}
