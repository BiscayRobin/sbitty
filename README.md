# sbitty: when standard bits become easy [![Build Status](https://travis-ci.org/BiscayRobin/sbitty.svg?branch=master)](https://travis-ci.org/BiscayRobin/sbitty) [![Crate](https://img.shields.io/crates/v/rand.svg)](https://crates.io/crates/sbitty) [![API](https://docs.rs/rand/badge.svg)](https://docs.rs/sbitty)

This crate aims to give simple interface to bit twiddling. There is lots of standard define behavior on bitwise operation like `& | ^ !` but none for single bit operations on the standard int.

Some crates emulate bitfield but i found it restrictive since on all my project i usually use those operations on extra bit of a usable number.

## Setup

In your Cargo.toml:
```toml
[dependencies]
sbitty = "^1.0.0"
```
In your source:

> ```RUST 
> use sbitty::{GetBits,SetBits,IndexError};
> ```

> ```RUST
> use sbitty::*;
> ```

> ```RUST
> use sbitty::GetBits;
> ```

