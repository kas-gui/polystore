//! Polymorphic data store (collection)

// TODO: no_std?

use std::any::{Any, TypeId};
use std::collections::hash_map as std_hm;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::Deref;
pub use std_hm::Keys;

/// Wrapper around Any supporting Drop
pub trait MaybeDrop: Any {}
impl<T: Any + ?Sized> MaybeDrop for T {}

// Copied from Rust's std library (impl for dyn Any)
impl dyn MaybeDrop {
    /// Returns `true` if the boxed type is the same as `T`.
    #[inline]
    pub fn is<T: Any>(&self) -> bool {
        // Get `TypeId` of the type this function is instantiated with.
        let t = TypeId::of::<T>();

        // Get `TypeId` of the type in the trait object (`self`).
        let concrete = self.type_id();

        // Compare both `TypeId`s on equality.
        t == concrete
    }

    /// Returns some reference to the boxed value if it is of type `T`, or `None` if it isn't.
    #[inline]
    pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
        if self.is::<T>() {
            // SAFETY: just checked whether we are pointing to the correct type, and we can rely on
            // that check for memory safety because we have implemented Any for all types; no other
            // impls can exist as they would conflict with our impl.
            unsafe { Some(&*(self as *const dyn MaybeDrop as *const T)) }
        } else {
            None
        }
    }

    /// Returns some mutable reference to the boxed value if it is of type `T`, or `None` if it isn't.
    #[inline]
    pub fn downcast_mut<T: Any>(&mut self) -> Option<&mut T> {
        if self.is::<T>() {
            // SAFETY: just checked whether we are pointing to the correct type, and we can rely on
            // that check for memory safety because we have implemented Any for all types; no other
            // impls can exist as they would conflict with our impl.
            unsafe { Some(&mut *(self as *mut dyn MaybeDrop as *mut T)) }
        } else {
            None
        }
    }
}

// Copied from Rust's std library (impl for dyn Any)
impl fmt::Debug for dyn MaybeDrop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MaybeDrop").finish_non_exhaustive()
    }
}

// Copied from Rust's std library (impl for Box<dyn Any>)
#[inline]
/// Attempt to downcast the box to a concrete type.
fn downcast_box<T: Any>(b: Box<dyn MaybeDrop>) -> Result<Box<T>, Box<dyn MaybeDrop>> {
    if b.is::<T>() {
        unsafe {
            let raw: *mut dyn MaybeDrop = Box::into_raw(b);
            Ok(Box::from_raw(raw as *mut T))
        }
    } else {
        Err(b)
    }
}

/// The polymorphic data store
///
/// Internally this uses a `HashMap` with boxed values, thus performance is
/// much like that of `HashMap`.
// TODO: this is a map... rename?
#[derive(Debug)]
// TODO: faster hash
// FIXME: we cannot Drop values!
pub struct Store<K>(HashMap<K, Box<dyn MaybeDrop>>);

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
    pub fn keys(&self) -> Keys<K, Box<dyn MaybeDrop>> {
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
        self.0.get(key).map(|v| v.type_id())
    }

    /// Returns a reference to the value corresponding to the key
    ///
    /// The value's type is inferred from the [`TaggedKey`].
    ///
    /// Returns `None` if no element matches `tag` or if the type `V` does not match the element.
    pub fn get_tagged<V: 'static>(&self, key: &TaggedKey<K, V>) -> Option<&V> {
        self.get::<V>(key)
    }

    /// Returns a reference to the value corresponding to the key
    ///
    /// The value's type must be specified explicitly.
    ///
    /// Returns `None` if no element matches `key`. Panics on type mismatch.
    pub fn get<V: 'static>(&self, key: &K) -> Option<&V> {
        self.0.get(key).and_then(|v| v.downcast_ref())
    }

    /// Returns a mutable reference to the value corresponding to the key
    pub fn get_tagged_mut<V: 'static>(&mut self, key: &TaggedKey<K, V>) -> Option<&mut V> {
        self.get_mut::<V>(key)
    }

    /// Returns a mutable reference to the value corresponding to the key
    ///
    /// Returns `None` if no element matches `key`. Panics on type mismatch.
    pub fn get_mut<V: 'static>(&mut self, key: &K) -> Option<&mut V> {
        self.0.get_mut(key).and_then(|v| v.downcast_mut())
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
        self.0.insert(key.clone(), Box::new(value));
        TaggedKey::new(key)
    }

    /// Removes and returns a value, if present
    ///
    /// Panics on type mismatch.
    pub fn remove_boxed<V: 'static>(&mut self, key: &TaggedKey<K, V>) -> Option<Box<V>> {
        self.0.remove(key).and_then(|v| downcast_box(v).ok())
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
    std_hm::OccupiedEntry<'a, K, Box<dyn MaybeDrop>>,
    PhantomData<V>,
);
impl<'a, K: 'a, V: 'static> OccupiedEntry<'a, K, V> {
    /// Get the entry
    ///
    /// Panics on type mismatch.
    pub fn get(&self) -> &V {
        self.0.get().downcast_ref().unwrap()
    }

    /// Get the entry, mutably
    ///
    /// Panics on type mismatch.
    pub fn get_mut(&mut self) -> &mut V {
        self.0.get_mut().downcast_mut().unwrap()
    }

    /// Convert into a mutable reference
    ///
    /// Panics on type mismatch.
    pub fn into_mut(self) -> &'a mut V {
        self.0.into_mut().downcast_mut().unwrap()
    }

    /// Sets the value of the entry
    pub fn insert(&mut self, value: V) -> Box<dyn MaybeDrop> {
        self.0.insert(Box::new(value))
    }

    /// Removes and returns the entry's value
    ///
    /// Panics on type mismatch.
    pub fn remove_boxed(self) -> Box<V> {
        downcast_box(self.0.remove()).unwrap()
    }
}

/// A vacant entry
pub struct VacantEntry<'a, K: 'a, V: 'static>(
    std_hm::VacantEntry<'a, K, Box<dyn MaybeDrop>>,
    PhantomData<V>,
);
impl<'a, K: 'a, V: 'static> VacantEntry<'a, K, V> {
    /// Sets the value of the entry and returns a mutable reference to it
    pub fn insert(self, value: V) -> &'a mut V {
        let v = self.0.insert(Box::new(value));
        v.downcast_mut().unwrap()
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
        assert_eq!(store.get_tagged(&k1), Some(&"another str"));

        let k2 = store.insert(2, "A String".to_string());
        assert_eq!(store.get_tagged(&k2), Some(&"A String".to_string()));

        assert!(store.contains_key(&k1));
        assert!(store.contains_key(&1));
        assert!(!store.contains_key(&3));
    }

    #[test]
    fn zero_sized() {
        let mut store = Store::new();
        let k = store.insert(1, ());
        assert_eq!(store.get_tagged(&k), Some(&()));
    }

    #[test]
    fn untyped_keys() {
        let mut store = Store::new();
        store.insert(1, ());
        assert_eq!(store.get(&1), Some(&()));
    }

    #[test]
    #[should_panic]
    fn incorrect_untyped_keys() {
        let mut store = Store::new();
        store.insert(1, ());
        assert_eq!(store.get(&1), Some(&1));
    }

    #[test]
    fn entry_api() {
        let mut store = Store::new();
        let k = 1;
        *store.entry(k).or_insert(0) = 10;
        assert_eq!(store.get(&k), Some(&10));

        *store.entry(k).or_insert(0) = 20;
        assert_eq!(store.get(&k), Some(&20));
    }
}
