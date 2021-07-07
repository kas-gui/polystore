//! Polymorphic data store (collection)

// TODO: no_std?

use std::any::{type_name, TypeId};
use std::collections::hash_map as std_hm;
use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;
use std::mem::size_of;
use std::ops::Deref;
use std::slice;
pub use std_hm::Keys;

type Erased = (TypeId, Box<[u8]>);

fn assert_type_id<V: 'static>(id: TypeId) {
    assert_eq!(
        id,
        TypeId::of::<V>(),
        "type V={} does not match type id",
        type_name::<V>()
    );
}

/// The polymorphic data store
///
/// Internally this uses a `HashMap` with boxed values, thus performance is
/// much like that of `HashMap`.
// TODO: this is a map... rename?
#[derive(Debug)]
// TODO: faster hash
// FIXME: we cannot Drop values!
pub struct Store<K>(HashMap<K, Erased>);

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
    // TODO: access to the hasher?

    /// Returns an iterator over all keys in arbitrary order
    ///
    /// These are *not* tagged keys; only the bare key is stored.
    pub fn keys(&self) -> Keys<K, (TypeId, Box<[u8]>)> {
        self.0.keys()
    }

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

    /// Get the [`TypeId`] of a stored value
    pub fn get_type_id(&self, key: &K) -> Option<TypeId> {
        self.0.get(key).map(|v| v.0)
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
    /// Returns `None` if no element matches `key`. Panics on type mismatch.
    pub fn get_typed<V: 'static>(&self, key: &K) -> Option<&V> {
        if let Some(v) = self.0.get(key) {
            assert_type_id::<V>(v.0);
            let slice: &[u8] = &*v.1;
            debug_assert_eq!(slice.len(), size_of::<V>());
            let p = slice.as_ptr() as *const u8 as *const V;
            return Some(unsafe { &*p });
        }
        None
    }

    /// Returns a mutable reference to the value corresponding to the key
    pub fn get_mut<V: 'static>(&mut self, key: &TaggedKey<K, V>) -> Option<&mut V> {
        self.get_typed_mut::<V>(key)
    }

    /// Returns a mutable reference to the value corresponding to the key
    ///
    /// Returns `None` if no element matches `key`. Panics on type mismatch.
    pub fn get_typed_mut<V: 'static>(&mut self, key: &K) -> Option<&mut V> {
        if let Some(v) = self.0.get_mut(key) {
            assert_type_id::<V>(v.0);
            let slice: &mut [u8] = &mut *v.1;
            debug_assert_eq!(slice.len(), size_of::<V>());
            let p = slice.as_mut_ptr() as *mut u8 as *mut V;
            return Some(unsafe { &mut *p });
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

    /// Removes and returns a value, if present
    ///
    /// Panics on type mismatch.
    pub fn remove_boxed<V: 'static>(&mut self, key: &TaggedKey<K, V>) -> Option<Box<V>> {
        self.0.remove(key).map(|v| {
            assert_type_id::<V>(v.0);
            unsafe {
                let slice: &mut [u8] = &mut *Box::into_raw(v.1);
                debug_assert_eq!(slice.len(), size_of::<V>());
                Box::from_raw(slice.as_mut_ptr() as *mut V)
            }
        })
    }

    /// Get `key`'s entry for in-place manipulation
    pub fn entry<V: 'static>(&mut self, key: K) -> Entry<K, V> {
        match self.0.entry(key) {
            std_hm::Entry::Occupied(entry) => {
                Entry::Occupied(OccupiedEntry(entry, Default::default()))
            }
            std_hm::Entry::Vacant(entry) => Entry::Vacant(VacantEntry(entry, Default::default())),
        }
    }
}

/// A view into a single entry in a map
pub enum Entry<'a, K: 'a, V: 'static> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K: 'a, V: 'static> Entry<'a, K, V> {
    /// Ensure a value exists and return its reference
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensure a value exists and return its reference
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }
}

/// An occupied entry
pub struct OccupiedEntry<'a, K: 'a, V: 'static>(
    std_hm::OccupiedEntry<'a, K, Erased>,
    PhantomData<V>,
);
impl<'a, K: 'a, V: 'static> OccupiedEntry<'a, K, V> {
    /// Get the entry
    ///
    /// Panics on type mismatch.
    pub fn get(&self) -> &V {
        let v = self.0.get();
        assert_type_id::<V>(v.0);
        let slice: &[u8] = &*v.1;
        debug_assert_eq!(slice.len(), size_of::<V>());
        let p = slice.as_ptr() as *const u8 as *const V;
        unsafe { &*p }
    }

    /// Get the entry, mutably
    ///
    /// Panics on type mismatch.
    pub fn get_mut(&mut self) -> &mut V {
        let v = self.0.get_mut();
        assert_type_id::<V>(v.0);
        let slice: &mut [u8] = &mut *v.1;
        debug_assert_eq!(slice.len(), size_of::<V>());
        let p = slice.as_ptr() as *mut u8 as *mut V;
        unsafe { &mut *p }
    }

    /// Convert into a mutable reference
    ///
    /// Panics on type mismatch.
    pub fn into_mut(self) -> &'a mut V {
        let v = self.0.into_mut();
        assert_type_id::<V>(v.0);
        let slice: &mut [u8] = &mut *v.1;
        debug_assert_eq!(slice.len(), size_of::<V>());
        let p = slice.as_ptr() as *mut u8 as *mut V;
        unsafe { &mut *p }
    }

    /// Sets the value of the entry
    pub fn insert(&mut self, value: V) {
        let boxed = Box::new(value);
        let type_erased = unsafe {
            let raw = Box::into_raw(boxed) as *mut u8;
            let slice = slice::from_raw_parts_mut(raw, size_of::<V>());
            Box::<[u8]>::from_raw(slice)
        };
        self.0.insert((TypeId::of::<V>(), type_erased));
    }

    /// Removes and returns the entry's value
    ///
    /// Panics on type mismatch.
    pub fn remove_boxed(self) -> Box<V> {
        let v = self.0.remove();
        assert_type_id::<V>(v.0);
        unsafe {
            let slice: &mut [u8] = &mut *Box::into_raw(v.1);
            debug_assert_eq!(slice.len(), size_of::<V>());
            Box::from_raw(slice.as_mut_ptr() as *mut V)
        }
    }
}

/// A vacant entry
pub struct VacantEntry<'a, K: 'a, V: 'static>(std_hm::VacantEntry<'a, K, Erased>, PhantomData<V>);
impl<'a, K: 'a, V: 'static> VacantEntry<'a, K, V> {
    /// Sets the value of the entry and returns a mutable reference to it
    pub fn insert(self, value: V) -> &'a mut V {
        let boxed = Box::new(value);
        let type_erased = unsafe {
            let raw = Box::into_raw(boxed) as *mut u8;
            let slice = slice::from_raw_parts_mut(raw, size_of::<V>());
            Box::<[u8]>::from_raw(slice)
        };
        let v = self.0.insert((TypeId::of::<V>(), type_erased));
        let slice: &mut [u8] = &mut *v.1;
        debug_assert_eq!(slice.len(), size_of::<V>());
        let p = slice.as_ptr() as *mut u8 as *mut V;
        unsafe { &mut *p }
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

    #[test]
    fn untyped_keys() {
        let mut store = Store::new();
        store.insert(1, ());
        assert_eq!(store.get_typed(&1), Some(&()));
    }

    #[test]
    #[should_panic]
    fn incorrect_untyped_keys() {
        let mut store = Store::new();
        store.insert(1, ());
        assert_eq!(store.get_typed(&1), Some(&1));
    }

    #[test]
    fn entry_api() {
        let mut store = Store::new();
        let k = 1;
        *store.entry(k).or_insert(0) = 10;
        assert_eq!(store.get_typed(&k), Some(&10));

        *store.entry(k).or_insert(0) = 20;
        assert_eq!(store.get_typed(&k), Some(&20));
    }
}
