# Polystore

[![Test Status](https://github.com/kas-gui/polystore/workflows/Tests/badge.svg?event=push)](https://github.com/kas-gui/polystore/actions)
[![Crate](https://img.shields.io/crates/v/polystore.svg)](https://crates.io/crates/polystore)
[![API](https://docs.rs/polystore/badge.svg)](https://docs.rs/polystore)

A polymorphic data store:
```rust
// It's a HashMap<K = i32> storing polymorphic values:
let mut store = HashMap::new();

// k1 is the key 1 tagged with the element type `&'static str`
let k1 = store.insert(1, "A static str");
if let Some(v) = store.get_mut(&k1) {
    *v = "another str";
}
assert_eq!(store.get_tagged(&k1), Some(&"another str"));

// untagged keys work too (relying on type inference, here `String`):
store.insert(2, "A String".to_string());
assert_eq!(store.get(&2), Some(&"A String".to_string()));

assert!(store.contains_key(&k1));
assert!(store.contains_key(&1));
assert!(!store.contains_key(&3));
```

## Crate Features

Optional crate features:

-   `fxhash`: add `FxHashMap` using the [rustc-hash](https://crates.io/crates/rustc-hash) crate

# License

Polystore is distributed under the terms of both the MIT license and the
Apache License (Version 2.0).

See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT), and
[COPYRIGHT](COPYRIGHT) for details.
