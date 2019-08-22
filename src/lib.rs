//! Standard integers does not have any standard implementation of bitwise
//! manipulation. This crate is made to fill this gap and hide ugly bitwise
//! operation which are error prone behind some runtime safe functions.
//!
//! It is made so you only have to call functions to use it properly.
//! This crate use indexes as you would in vectors or Arrays. If any
//! index error happend in your program you will get `Option<T>` or
//! `Result<_,_>` returned to properly handle this in a production ready
//! manner.
#![no_std]
use core::mem::size_of;

/// The IndexError enum is used for error handling
/// This should not be seen as an API user
pub enum IndexError {
	/// Thrown when an you wan't to acces too far in memory
	UNDERSIZED,
}

/// performing _ & (1 << idx) with n the index
///
/// # Examples
///
/// ## Getting bits in an u8
///
/// ```
/// assert_eq!(0b1000_0000u8.get_bit( 7 ) , Some(true));
/// assert_eq!(0b1111_1110u8.get_bit( 0 ) , Some(false));
/// assert_eq!(0b0000_0000u8.get_bit( 8 ) , None);
/// ```
pub trait GetBit {
	fn get_bit(&self, idx: usize) -> Option<bool>;
}

macro_rules! get_bit_impl {
	($($t:ty)*) => ($(
		impl GetBit for $t {
			fn get_bit(&self, idx: usize) -> Option<bool> {
				if idx >= (size_of::<Self>() * 8) {
					None
				} else if *self & (1 << idx) != 0 {
					Some(true)
				} else {
					Some(false)
				}
			}
		}
	)*)
}

get_bit_impl! {u8 u16 u32 u64 usize i8 i16 i32 i64 isize}

pub trait SetBit {
	fn set_bit(&self, idx: usize) -> Result<Self, IndexError>
	where
		Self: Sized;
}

macro_rules! set_bit_impl {
	($($t:ty)*) => ($(
		impl SetBit for $t {
			fn set_bit(&self, idx: usize) -> Result<Self, IndexError> where Self: Sized {
				if idx >= (size_of::<Self>() * 8) {
					Err(IndexError::UNDERSIZED)
				} else {
					Ok(*self | (1 << idx))
				}
			}
		}
	)*)
}

set_bit_impl! {u8 u16 u32 u64 usize i8 i16 i32 i64 isize}

pub trait UnsetBit {
	fn unset_bit(&self, idx: usize) -> Result<Self, IndexError>
	where
		Self: Sized;
}

pub trait ToggleBit {
	fn toggle_bit(&self, idx: usize) -> Result<Self, IndexError>
	where
		Self: Sized;
}
#[cfg(test)]
mod test {
	use super::*;
	#[test]
	fn get_bit_u8() {
		assert_eq!(0u8.get_bit(0), Some(false));
		assert_eq!(1u8.get_bit(0), Some(true));
		assert_eq!(0u8.get_bit(size_of::<u8>() * 8), None);
	}
	#[test]
	fn get_bit_u16() {
		assert_eq!(0u16.get_bit(0), Some(false));
		assert_eq!(1u16.get_bit(0), Some(true));
		assert_eq!(0u16.get_bit(size_of::<u16>() * 8), None);
	}
	#[test]
	fn get_bit_u32() {
		assert_eq!(0u32.get_bit(0), Some(false));
		assert_eq!(1u32.get_bit(0), Some(true));
		assert_eq!(0u32.get_bit(size_of::<u32>() * 8), None);
	}
	#[test]
	fn get_bit_u64() {
		assert_eq!(0u64.get_bit(0), Some(false));
		assert_eq!(1u64.get_bit(0), Some(true));
		assert_eq!(0u64.get_bit(size_of::<u64>() * 8), None);
	}
	#[test]
	fn get_bit_usize() {
		assert_eq!(0usize.get_bit(0), Some(false));
		assert_eq!(1usize.get_bit(0), Some(true));
		assert_eq!(0usize.get_bit(size_of::<usize>() * 8), None);
	}
	#[test]
	fn get_bit_i8() {
		assert_eq!(0i8.get_bit(0), Some(false));
		assert_eq!(1i8.get_bit(0), Some(true));
		assert_eq!(0i8.get_bit(size_of::<i8>() * 8), None);
	}
	#[test]
	fn get_bit_i16() {
		assert_eq!(0i16.get_bit(0), Some(false));
		assert_eq!(1i16.get_bit(0), Some(true));
		assert_eq!(0i16.get_bit(size_of::<i16>() * 8), None);
	}
	#[test]
	fn get_bit_i32() {
		assert_eq!(0i32.get_bit(0), Some(false));
		assert_eq!(1i32.get_bit(0), Some(true));
		assert_eq!(0i32.get_bit(size_of::<i32>() * 8), None);
	}
	#[test]
	fn get_bit_i64() {
		assert_eq!(0i64.get_bit(0), Some(false));
		assert_eq!(1i64.get_bit(0), Some(true));
		assert_eq!(0i64.get_bit(size_of::<i64>() * 8), None);
	}
	#[test]
	fn get_bit_isize() {
		assert_eq!(0isize.get_bit(0), Some(false));
		assert_eq!(1isize.get_bit(0), Some(true));
		assert_eq!(0isize.get_bit(size_of::<isize>() * 8), None);
	}

	#[test]
	fn set_bit_u8() {
		assert_eq!(1u8.set_bit(0).ok(), Some(1));
		assert_eq!(0u8.set_bit(0).ok(), Some(1));
		assert!(0u8.set_bit(size_of::<u8>() * 8).is_err());
	}
	#[test]
	fn set_bit_u16() {
		assert_eq!(1u16.set_bit(0).ok(), Some(1));
		assert_eq!(0u16.set_bit(0).ok(), Some(1));
		assert!(0u16.set_bit(size_of::<u16>() * 8).is_err());
	}
	#[test]
	fn set_bit_u32() {
		assert_eq!(1u32.set_bit(0).ok(), Some(1));
		assert_eq!(0u32.set_bit(0).ok(), Some(1));
		assert!(0u32.set_bit(size_of::<u32>() * 8).is_err());
	}
	#[test]
	fn set_bit_u64() {
		assert_eq!(1u64.set_bit(0).ok(), Some(1));
		assert_eq!(0u64.set_bit(0).ok(), Some(1));
		assert!(0u64.set_bit(size_of::<u64>() * 8).is_err());
	}
	#[test]
	fn set_bit_usize() {
		assert_eq!(1usize.set_bit(0).ok(), Some(1));
		assert_eq!(0usize.set_bit(0).ok(), Some(1));
		assert!(0usize.set_bit(size_of::<usize>() * 8).is_err());
	}
	#[test]
	fn set_bit_i8() {
		assert_eq!(0i8.set_bit(0).ok(), Some(1));
		assert_eq!(0i8.set_bit(0).ok(), Some(1));
		assert!(0i8.set_bit(size_of::<i8>() * 8).is_err());
	}
	#[test]
	fn set_bit_i16() {
		assert_eq!(0i16.set_bit(0).ok(), Some(1));
		assert_eq!(0i16.set_bit(0).ok(), Some(1));
		assert!(0i16.set_bit(size_of::<i16>() * 8).is_err());
	}
	#[test]
	fn set_bit_i32() {
		assert_eq!(0i32.set_bit(0).ok(), Some(1));
		assert_eq!(0i32.set_bit(0).ok(), Some(1));
		assert!(0i32.set_bit(size_of::<i32>() * 8).is_err());
	}
	#[test]
	fn set_bit_i64() {
		assert_eq!(0i64.set_bit(0).ok(), Some(1));
		assert_eq!(0i64.set_bit(0).ok(), Some(1));
		assert!(0i64.set_bit(size_of::<i64>() * 8).is_err());
	}
	#[test]
	fn set_bit_isize() {
		assert_eq!(0isize.set_bit(0).ok(), Some(1));
		assert_eq!(0isize.set_bit(0).ok(), Some(1));
		assert!(0isize.set_bit(size_of::<isize>() * 8).is_err());
	}
}
