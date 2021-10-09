# Rust port of libdivide

For the purpose of original libdivide, see [libdivide.com](https://libdivide.com/).

This is port of libdivide 4.0 with scalars support.

Cargo crate name is [libdivide](https://crates.io/crates/libdivide)

# Example

```rust
use libdivide::Divider;

let d = Divider(5);  // this is slow
let r = 100 / &d;  // this is fast
```
