//! FastString: A flexible, easy-to-use, immutable, efficient `String` replacement for Rust.
//!
//! ## What is FastString
//! [FastString] is a read-only string wrapper. You can think of it as an ownership `&str` type.
//! FastString uses three variants of `&'static str`, `Arc<String>` and `StackString`, and automatically selects the best storage method;
//! And optimized string cloning and string comparison.
//!
//! ## What Is It For?
//! [FastString] is better than String as long as it is not often necessary to modify strings and connect strings.
//!
//! ## How To Use It?
//! String constants are easily wrapped into the unified [FastString] type. For other string types, different types of storage will be automatically selected.
//! ```
//! use fast_str::FastString;
//! // compile-time constants
//! const EMPTY_STR: FastString = FastString::new();
//! const STATIC_STR: FastString = FastString::from_static("💙❤");
//!
//! let str1: FastString = "🍷 wink".into();
//! // String storage is used in 32-bit machines,
//! // and stack memory is used in 64 bit machines to store strings
//! let str2 = FastString::from_ref("😆 Happy");
//!
//! // You can use the operator '+' to connect strings.
//! let str3: FastString = str1 + str2;
//!
//! // O(1) Clone() of time complexity.
//! let str4: FastString = str3.clone();
//!
//! // You can use String as the storage variant of FastString,
//! // and when FastString has the sole ownership of the String variant,
//! // no performance consumption is converted to the String type.
//! let from_string = FastString::from_string(String::from("hello world"));
//! let from_faststr = String::from(from_string);
//! ```
//!
//! ## Feature Flags
//!
//! `fast-str` comes with optional support for the following crates through Cargo
//! feature flags. You can enable them in your `Cargo.toml` file like this:
//!
//! ```no_compile
//! [dependencies]
//! fast-str = { version = "*", features = ["rocket", "serde"] }
//! ```
//!
//! | Feature | Description |
//! | ------- | ----------- |
//! | [`arbitrary`](https://crates.io/crates/arbitrary) | [`Arbitrary`](https://docs.rs/arbitrary/latest/arbitrary/trait.Arbitrary.html) implementation for [`FastString`]. |
//! | [`rocket`](https://crates.io/crates/rocket) | [`Responder`](https://api.rocket.rs/v0.4/rocket/response/trait.Responder.html) implementation for [`FastString`]. |
//! | [`actix`](https://crates.io/crates/actix-web) | [`Responder`](https://docs.rs/actix-web/latest/actix_web/trait.Responder.html) implementation for [`FastString`]. |
//! | [`serde`](https://crates.io/crates/serde) | [`Serialize`](https://docs.rs/arbitrary/latest/arbitrary/trait.Arbitrary.html) and [`Deserialize`](https://docs.rs/serde/latest/serde/trait.Deserialize.html) implementations for [`FastString`]. |

mod backend;
mod iter;
mod normal;
mod pattern;
mod stack;

pub use self::backend::FastString;
