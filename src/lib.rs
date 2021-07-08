//! Polymorphic data store (collection)

// TODO: support other collection types? If so, we can support `no_std` too.

use std::any::{Any, TypeId};
use std::collections::hash_map as std_hm;
use std::hash::{BuildHasher, Hash};
use std::marker::PhantomData;
use std::ops::Deref;
pub use std_hm::Keys;

/// The polymorphic data store
///
/// Internally this uses a `HashMap` with boxed values, thus performance is
/// much like that of `HashMap`.
///
/// Note: [`HashMap`]'s capacity reservation API is excluded. There is no
/// fundamental reason for this, other than each stored value requiring an
/// allocation (boxing) anyway.
///
/// # Warning
///
/// **Warning:** values stored in the map will not have their destructor
/// ([`Drop::drop`]) run when the map is destroyed. This is not currently
/// fixable (`min_specialization` +
/// <https://github.com/rust-lang/rust/issues/46893> may be sufficient).
#[derive(Debug)]
pub struct HashMap<K, S>(std_hm::HashMap<K, Box<dyn Any>, S>);

#[cfg(feature = "fxhash")]
pub type FxHashMap<K> = HashMap<K, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;

impl<K, S: Default> Default for HashMap<K, S> {
    fn default() -> Self {
        HashMap::with_hasher(Default::default())
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

impl<K> HashMap<K, std_hm::RandomState> {
    /// Construct a new store
    pub fn new() -> Self {
        Default::default()
    }
}

impl<K, S> HashMap<K, S> {
    /// Construct a new store with the given hash bulider
    pub fn with_hasher(hash_builder: S) -> Self {
        HashMap(std_hm::HashMap::with_hasher(hash_builder))
    }

    /// Return's a reference to the map's [`std::hash::HashBuilder`]
    pub fn hasher(&self) -> &S {
        self.0.hasher()
    }

    /// Returns an iterator over all keys in arbitrary order
    ///
    /// These are *not* tagged keys; only the bare key is stored.
    pub fn keys(&self) -> Keys<K, Box<dyn Any>> {
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

impl<K: Eq + Hash, S: BuildHasher> HashMap<K, S> {
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
    #[inline]
    pub fn insert<V: 'static>(&mut self, key: K, value: V) -> TaggedKey<K, V>
    where
        K: Clone,
    {
        self.insert_boxed(key, Box::new(value))
    }

    /// Inserts a key and boxed value pair
    ///
    /// Returns the corresponding [`TaggedKey`] for convenience.
    ///
    /// Unlike [`HashMap`] this does not return any displaced old value since
    /// the type of any such value is unknown.
    pub fn insert_boxed<V: 'static>(&mut self, key: K, value: Box<V>) -> TaggedKey<K, V>
    where
        K: Clone,
    {
        self.0.insert(key.clone(), value);
        TaggedKey::new(key)
    }

    /// Removes and returns a value, if present
    ///
    /// Panics on type mismatch.
    pub fn remove<V: 'static>(&mut self, key: &TaggedKey<K, V>) -> Option<V> {
        self.remove_boxed(key).map(|v| *v)
    }

    /// Removes and returns a value, if present
    ///
    /// Panics on type mismatch.
    pub fn remove_boxed<V: 'static>(&mut self, key: &TaggedKey<K, V>) -> Option<Box<V>> {
        self.0.remove(key).and_then(|v| v.downcast().ok())
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
    std_hm::OccupiedEntry<'a, K, Box<dyn Any>>,
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
    pub fn insert(&mut self, value: V) -> Box<dyn Any> {
        self.0.insert(Box::new(value))
    }

    /// Removes and returns the entry's value
    ///
    /// Panics on type mismatch.
    pub fn remove_boxed(self) -> Box<V> {
        self.0.remove().downcast().unwrap()
    }
}

/// A vacant entry
pub struct VacantEntry<'a, K: 'a, V: 'static>(
    std_hm::VacantEntry<'a, K, Box<dyn Any>>,
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
        let mut store = HashMap::new();

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
        let mut store = HashMap::new();
        let k = store.insert(1, ());
        assert_eq!(store.get_tagged(&k), Some(&()));
    }

    #[test]
    fn untyped_keys() {
        let mut store = HashMap::new();
        store.insert(1, ());
        assert_eq!(store.get(&1), Some(&()));
    }

    #[test]
    #[should_panic]
    fn incorrect_untyped_keys() {
        let mut store = HashMap::new();
        store.insert(1, ());
        assert_eq!(store.get(&1), Some(&1));
    }

    #[test]
    fn entry_api() {
        let mut store = HashMap::new();
        let k = 1;
        *store.entry(k).or_insert(0) = 10;
        assert_eq!(store.get(&k), Some(&10));

        *store.entry(k).or_insert(0) = 20;
        assert_eq!(store.get(&k), Some(&20));
    }
}
