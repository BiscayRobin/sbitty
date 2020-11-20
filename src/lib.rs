//! Standard integers does not have any standard implementation of bitwise
//! manipulation. This crate is made to fill this gap and hide ugly bitwise
//! operation which are error prone behind some runtime safe functions.
//!
//! It is made so you only have to call functions to use it properly.
//! This crate use indexes as you would in vectors or Arrays. If any
//! index error happened in your program you will get `Option<T>` or
//! `Result<_,_>` returned to properly handle this in a production ready
//! manner.
#![no_std]
use core::mem::size_of;

/// The IndexError struct is used for error handling
/// This should not be seen as an API user
pub struct IndexError;

/// performing _ & (1 << idx) with n the index and return the boolean corresponding
///
/// # Examples
///
/// ## get bit for big int
///
/// Don't pay attention to my bigint implementation.
///
/// ```
/// pub struct BigInt {
/// 	hwb: i64,
/// 	lwb: i64,
/// }
/// # pub trait GetBit {
/// # 	fn get_bit(&self, idx: usize) -> Option<bool>;
/// # }
/// impl GetBit for BigInt {
/// 	fn get_bit(&self, idx: usize) -> Option<bool> {
/// 		if idx >= 128 {
/// 			None
/// 		} else if idx >= 64 {
/// 			if self.hwb & (1 << (idx - 64)) != 0 {
/// 				Some(true)
/// 			}
/// 			else {
/// 				Some(false)
/// 			}
/// 		} else {
/// 			if self.lwb & (1 << idx) != 0 {
/// 				Some(true)
/// 			}
/// 			else {
/// 				Some(false)
/// 			}
/// 		}
/// 	}
/// }
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

/// performing _ | (1 << idx) with n the index
///
/// # Examples
///
/// ## set bit for big int
///
/// Don't pay attention to my bigint implementation.
///
/// ```
/// pub struct BigInt {
/// 	hwb: i64,
/// 	lwb: i64,
/// }
/// # pub struct IndexError;
/// # pub trait SetBit {
/// # 	fn set_bit(&self, idx: usize) -> Result<Self,IndexError> where Self: Sized;
/// # }
/// impl SetBit for BigInt {
/// 	fn set_bit(&self, idx: usize) -> Result<Self,IndexError> where Self: Sized {
/// 		if idx >= 128 {
/// 			Err(IndexError)
/// 		} else if idx >= 64 {
/// 			Ok(BigInt{
/// 				hwb: self.hwb | (1 << (idx - 64)),
/// 				lwb: self.lwb
/// 			})
/// 		} else {
/// 			Ok(BigInt{
/// 				hwb: self.hwb,
/// 				lwb: self.lwb | (1 << (idx - 64))
/// 			})
/// 		}
/// 	}
/// }
/// ```
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
					Err(IndexError)
				} else {
					Ok(*self | (1 << idx))
				}
			}
		}
	)*)
}

set_bit_impl! {u8 u16 u32 u64 usize i8 i16 i32 i64 isize}

/// performing _ & !(1 << idx) with n the index
///
/// # Examples
///
/// ## unset bit for big int
///
/// Don't pay attention to my bigint implementation.
///
/// ```
/// pub struct BigInt {
/// 	hwb: i64,
/// 	lwb: i64,
/// }
/// # pub struct IndexError;
/// # pub trait UnsetBit {
/// # 	fn unset_bit(&self, idx: usize) -> Result<Self,IndexError> where Self: Sized;
/// # }
/// impl UnsetBit for BigInt {
/// 	fn unset_bit(&self, idx: usize) -> Result<Self,IndexError> where Self: Sized {
/// 		if idx >= 128 {
/// 			Err(IndexError)
/// 		} else if idx >= 64 {
/// 			Ok(BigInt{
/// 				hwb: self.hwb & !(1 << (idx - 64)),
/// 				lwb: self.lwb
/// 			})
/// 		} else {
/// 			Ok(BigInt{
/// 				hwb: self.hwb,
/// 				lwb: self.lwb & !(1 << (idx - 64))
/// 			})
/// 		}
/// 	}
/// }
/// ```
pub trait UnsetBit {
	fn unset_bit(&self, idx: usize) -> Result<Self, IndexError>
	where
		Self: Sized;
}

macro_rules! unset_bit_impl {
	($($t:ty)*) => ($(
		impl UnsetBit for $t {
			fn unset_bit(&self, idx: usize) -> Result<Self, IndexError> where Self: Sized {
				if idx >= (size_of::<Self>() * 8) {
					Err(IndexError)
				} else {
					Ok(*self & !(1 << idx))
				}
			}
		}
	)*)
}

unset_bit_impl! {u8 u16 u32 u64 usize i8 i16 i32 i64 isize}

/// performing _ ^ (1 << idx) with n the index
///
/// # Examples
///
/// ## unset bit for big int
///
/// Don't pay attention to my bigint implementation.
///
/// ```
/// pub struct BigInt {
/// 	hwb: i64,
/// 	lwb: i64,
/// }
/// # pub struct IndexError;
/// # pub trait ToggleBit {
/// # 	fn toggle_bit(&self, idx: usize) -> Result<Self,IndexError> where Self: Sized;
/// # }
/// impl ToggleBit for BigInt {
/// 	fn toggle_bit(&self, idx: usize) -> Result<Self,IndexError> where Self: Sized {
/// 		if idx >= 128 {
/// 			Err(IndexError)
/// 		} else if idx >= 64 {
/// 			Ok(BigInt{
/// 				hwb: self.hwb ^ (1 << (idx - 64)),
/// 				lwb: self.lwb
/// 			})
/// 		} else {
/// 			Ok(BigInt{
/// 				hwb: self.hwb,
/// 				lwb: self.lwb ^ (1 << (idx - 64))
/// 			})
/// 		}
/// 	}
/// }
/// ```
pub trait ToggleBit {
	fn toggle_bit(&self, idx: usize) -> Result<Self, IndexError>
	where
		Self: Sized;
}

macro_rules! toggle_bit_impl {
	($($t:ty)*) => ($(
		impl ToggleBit for $t {
			fn toggle_bit(&self, idx: usize) -> Result<Self, IndexError> where Self: Sized {
				if idx >= (size_of::<Self>() * 8) {
					Err(IndexError)
				} else {
					Ok(*self ^ (1 << idx))
				}
			}
		}
	)*)
}

toggle_bit_impl! {u8 u16 u32 u64 usize i8 i16 i32 i64 isize}

#[cfg(test)]
mod test {
	use super::*;
	#[test]
	fn get_bit_u8() {
		assert_eq!(0u8.get_bit(0), Some(false));
		assert_eq!(1u8.get_bit(0), Some(true));
		assert_eq!(0x4u8.get_bit(2), Some(true));
		assert_eq!((!0x4u8).get_bit(2), Some(false));
		assert_eq!(0u8.get_bit(size_of::<u8>() * 8), None);
	}
	#[test]
	fn get_bit_u16() {
		assert_eq!(0u16.get_bit(0), Some(false));
		assert_eq!(1u16.get_bit(0), Some(true));
		assert_eq!(0x4u16.get_bit(2), Some(true));
		assert_eq!((!0x4u16).get_bit(2), Some(false));
		assert_eq!(0u16.get_bit(size_of::<u16>() * 8), None);
	}
	#[test]
	fn get_bit_u32() {
		assert_eq!(0u32.get_bit(0), Some(false));
		assert_eq!(1u32.get_bit(0), Some(true));
		assert_eq!(0x4u32.get_bit(2), Some(true));
		assert_eq!((!0x4u32).get_bit(2), Some(false));
		assert_eq!(0u32.get_bit(size_of::<u32>() * 8), None);
	}
	#[test]
	fn get_bit_u64() {
		assert_eq!(0u64.get_bit(0), Some(false));
		assert_eq!(1u64.get_bit(0), Some(true));
		assert_eq!(0x4u64.get_bit(2), Some(true));
        assert_eq!((!0x4u64).get_bit(2), Some(false));
		assert_eq!(0u64.get_bit(size_of::<u64>() * 8), None);
	}
	#[test]
	fn get_bit_usize() {
		assert_eq!(0usize.get_bit(0), Some(false));
		assert_eq!(1usize.get_bit(0), Some(true));
		assert_eq!(0x4usize.get_bit(2), Some(true));
		assert_eq!((!0x4usize).get_bit(2), Some(false));
		assert_eq!(0usize.get_bit(size_of::<usize>() * 8), None);
	}
	#[test]
	fn get_bit_i8() {
		assert_eq!(0i8.get_bit(0), Some(false));
		assert_eq!(1i8.get_bit(0), Some(true));
		assert_eq!(0x4i8.get_bit(2), Some(true));
		assert_eq!((!0x4i8).get_bit(2), Some(false));
		assert_eq!(0i8.get_bit(size_of::<i8>() * 8), None);
	}
	#[test]
	fn get_bit_i16() {
		assert_eq!(0i16.get_bit(0), Some(false));
		assert_eq!(1i16.get_bit(0), Some(true));
		assert_eq!(0x4i16.get_bit(2), Some(true));
		assert_eq!((!0x4i16).get_bit(2), Some(false));
        assert_eq!(0i16.get_bit(size_of::<i16>() * 8), None);
	}
	#[test]
	fn get_bit_i32() {
		assert_eq!(0i32.get_bit(0), Some(false));
		assert_eq!(1i32.get_bit(0), Some(true));
		assert_eq!(0x4i32.get_bit(2), Some(true));
		assert_eq!((!0x4i32).get_bit(2), Some(false));
        assert_eq!(0i32.get_bit(size_of::<i32>() * 8), None);
	}
	#[test]
	fn get_bit_i64() {
		assert_eq!(0i64.get_bit(0), Some(false));
		assert_eq!(1i64.get_bit(0), Some(true));
		assert_eq!(0x4i64.get_bit(2), Some(true));
		assert_eq!((!0x4i64).get_bit(2), Some(false));
        assert_eq!(0i64.get_bit(size_of::<i64>() * 8), None);
	}
	#[test]
	fn get_bit_isize() {
		assert_eq!(0isize.get_bit(0), Some(false));
		assert_eq!(1isize.get_bit(0), Some(true));
		assert_eq!(0x4isize.get_bit(2), Some(true));
		assert_eq!((!0x4isize).get_bit(2), Some(false));
        assert_eq!(0isize.get_bit(size_of::<isize>() * 8), None);
	}

	#[test]
	fn set_bit_u8() {
		assert_eq!(1u8.set_bit(0).ok(), Some(1));
		assert_eq!(0u8.set_bit(0).ok(), Some(1));
		assert_eq!(0x4u8.set_bit(2).ok(), Some(0x4));
        assert_eq!((!0x4u8).set_bit(2).ok(), Some(!0u8));
        assert!(0u8.set_bit(size_of::<u8>() * 8).is_err());
	}
	#[test]
	fn set_bit_u16() {
		assert_eq!(1u16.set_bit(0).ok(), Some(1));
		assert_eq!(0u16.set_bit(0).ok(), Some(1));
		assert_eq!(0x4u16.set_bit(2).ok(), Some(0x4));
        assert_eq!((!0x4u16).set_bit(2).ok(), Some(!0u16));
        assert!(0u16.set_bit(size_of::<u16>() * 8).is_err());
	}
	#[test]
	fn set_bit_u32() {
		assert_eq!(1u32.set_bit(0).ok(), Some(1));
		assert_eq!(0u32.set_bit(0).ok(), Some(1));
		assert_eq!(0x4u32.set_bit(2).ok(), Some(0x4));
        assert_eq!((!0x4u32).set_bit(2).ok(), Some(!0u32));
        assert!(0u32.set_bit(size_of::<u32>() * 8).is_err());
	}
	#[test]
	fn set_bit_u64() {
		assert_eq!(1u64.set_bit(0).ok(), Some(1));
		assert_eq!(0u64.set_bit(0).ok(), Some(1));
		assert_eq!(0x4u64.set_bit(2).ok(), Some(0x4));
        assert_eq!((!0x4u64).set_bit(2).ok(), Some(!0u64));
        assert!(0u64.set_bit(size_of::<u64>() * 8).is_err());
	}
	#[test]
	fn set_bit_usize() {
		assert_eq!(1usize.set_bit(0).ok(), Some(1));
		assert_eq!(0usize.set_bit(0).ok(), Some(1));	
        assert_eq!(0x4usize.set_bit(2).ok(), Some(0x4));
        assert_eq!((!0x4usize).set_bit(2).ok(), Some(!0usize));
        assert!(0usize.set_bit(size_of::<usize>() * 8).is_err());
	}
	#[test]
	fn set_bit_i8() {
		assert_eq!(1i8.set_bit(0).ok(), Some(1));
		assert_eq!(0i8.set_bit(0).ok(), Some(1));
		assert_eq!(0x4i8.set_bit(2).ok(), Some(0x4));
        assert_eq!((!0x4i8).set_bit(2).ok(), Some(!0i8));
        assert!(0i8.set_bit(size_of::<i8>() * 8).is_err());
	}
	#[test]
	fn set_bit_i16() {
		assert_eq!(1i16.set_bit(0).ok(), Some(1));
		assert_eq!(0i16.set_bit(0).ok(), Some(1));
		assert_eq!(0x4i16.set_bit(2).ok(), Some(0x4));
        assert_eq!((!0x4i16).set_bit(2).ok(), Some(!0i16));
        assert!(0i16.set_bit(size_of::<i16>() * 8).is_err());
	}
	#[test]
	fn set_bit_i32() {
		assert_eq!(1i32.set_bit(0).ok(), Some(1));
		assert_eq!(0i32.set_bit(0).ok(), Some(1));
		assert_eq!(0x4i32.set_bit(2).ok(), Some(0x4));
        assert_eq!((!0x4i32).set_bit(2).ok(), Some(!0i32));
        assert!(0i32.set_bit(size_of::<i32>() * 8).is_err());
	}
	#[test]
	fn set_bit_i64() {
		assert_eq!(1i64.set_bit(0).ok(), Some(1));
		assert_eq!(0i64.set_bit(0).ok(), Some(1));
		assert_eq!(0x4i64.set_bit(2).ok(), Some(0x4));
        assert_eq!((!0x4i64).set_bit(2).ok(), Some(!0i64));
        assert!(0i64.set_bit(size_of::<i64>() * 8).is_err());
	}
	#[test]
	fn set_bit_isize() {
		assert_eq!(1isize.set_bit(0).ok(), Some(1));
		assert_eq!(0isize.set_bit(0).ok(), Some(1));
		assert_eq!(0x4isize.set_bit(2).ok(), Some(0x4));
        assert_eq!((!0x4isize).set_bit(2).ok(), Some(!0isize));
        assert!(0isize.set_bit(size_of::<isize>() * 8).is_err());
	}
	#[test]
	fn unset_bit_u8() {
		assert_eq!(1u8.unset_bit(0).ok(), Some(0));
		assert_eq!(0u8.unset_bit(0).ok(), Some(0));
		assert!(0u8.unset_bit(size_of::<u8>() * 8).is_err());
	}
	#[test]
	fn unset_bit_u16() {
		assert_eq!(1u16.unset_bit(0).ok(), Some(0));
		assert_eq!(0u16.unset_bit(0).ok(), Some(0));
		assert!(0u16.unset_bit(size_of::<u16>() * 8).is_err());
	}
	#[test]
	fn unset_bit_u32() {
		assert_eq!(1u32.unset_bit(0).ok(), Some(0));
		assert_eq!(0u32.unset_bit(0).ok(), Some(0));
		assert!(0u32.unset_bit(size_of::<u32>() * 8).is_err());
	}
	#[test]
	fn unset_bit_u64() {
		assert_eq!(1u64.unset_bit(0).ok(), Some(0));
		assert_eq!(0u64.unset_bit(0).ok(), Some(0));
		assert!(0u64.unset_bit(size_of::<u64>() * 8).is_err());
	}
	#[test]
	fn unset_bit_usize() {
		assert_eq!(1usize.unset_bit(0).ok(), Some(0));
		assert_eq!(0usize.unset_bit(0).ok(), Some(0));
		assert!(0usize.unset_bit(size_of::<usize>() * 8).is_err());
	}
	#[test]
	fn unset_bit_i8() {
		assert_eq!(1i8.unset_bit(0).ok(), Some(0));
		assert_eq!(0i8.unset_bit(0).ok(), Some(0));
		assert!(0i8.unset_bit(size_of::<i8>() * 8).is_err());
	}
	#[test]
	fn unset_bit_i16() {
		assert_eq!(1i16.unset_bit(0).ok(), Some(0));
		assert_eq!(0i16.unset_bit(0).ok(), Some(0));
		assert!(0i16.unset_bit(size_of::<i16>() * 8).is_err());
	}
	#[test]
	fn unset_bit_i32() {
		assert_eq!(1i32.unset_bit(0).ok(), Some(0));
		assert_eq!(0i32.unset_bit(0).ok(), Some(0));
		assert!(0i32.unset_bit(size_of::<i32>() * 8).is_err());
	}
	#[test]
	fn unset_bit_i64() {
		assert_eq!(1i64.unset_bit(0).ok(), Some(0));
		assert_eq!(0i64.unset_bit(0).ok(), Some(0));
		assert!(0i64.unset_bit(size_of::<i64>() * 8).is_err());
	}
	#[test]
	fn unset_bit_isize() {
		assert_eq!(1isize.unset_bit(0).ok(), Some(0));
		assert_eq!(0isize.unset_bit(0).ok(), Some(0));
		assert!(0isize.unset_bit(size_of::<isize>() * 8).is_err());
	}
	#[test]
	fn toggle_bit_u8() {
		assert_eq!(0b01u8.toggle_bit(1).ok(), Some(0b11));
		assert_eq!(0b01u8.toggle_bit(0).ok(), Some(0b00));
		assert!(0u8.toggle_bit(size_of::<u8>() * 8).is_err());
	}
	#[test]
	fn toggle_bit_u16() {
		assert_eq!(0b01u16.toggle_bit(1).ok(), Some(0b11));
		assert_eq!(0b01u16.toggle_bit(0).ok(), Some(0b00));
		assert!(0u16.toggle_bit(size_of::<u16>() * 8).is_err());
	}
	#[test]
	fn toggle_bit_u32() {
		assert_eq!(0b01u32.toggle_bit(1).ok(), Some(0b11));
		assert_eq!(0b01u32.toggle_bit(0).ok(), Some(0b00));
		assert!(0u32.toggle_bit(size_of::<u32>() * 8).is_err());
	}
	#[test]
	fn toggle_bit_u64() {
		assert_eq!(0b01u64.toggle_bit(1).ok(), Some(0b11));
		assert_eq!(0b01u64.toggle_bit(0).ok(), Some(0b00));
		assert!(0u64.toggle_bit(size_of::<u64>() * 8).is_err());
	}
	#[test]
	fn toggle_bit_usize() {
		assert_eq!(0b01usize.toggle_bit(1).ok(), Some(0b11));
		assert_eq!(0b01usize.toggle_bit(0).ok(), Some(0b00));
		assert!(0usize.toggle_bit(size_of::<usize>() * 8).is_err());
	}
	#[test]
	fn toggle_bit_i8() {
		assert_eq!(0b01i8.toggle_bit(1).ok(), Some(0b11));
		assert_eq!(0b01i8.toggle_bit(0).ok(), Some(0b00));
		assert!(0i8.toggle_bit(size_of::<i8>() * 8).is_err());
	}
	#[test]
	fn toggle_bit_i16() {
		assert_eq!(0b01i16.toggle_bit(1).ok(), Some(0b11));
		assert_eq!(0b01i16.toggle_bit(0).ok(), Some(0b00));
		assert!(0i16.toggle_bit(size_of::<i16>() * 8).is_err());
	}
	#[test]
	fn toggle_bit_i32() {
		assert_eq!(0b01i32.toggle_bit(1).ok(), Some(0b11));
		assert_eq!(0b01i32.toggle_bit(0).ok(), Some(0b00));
		assert!(0i32.toggle_bit(size_of::<i32>() * 8).is_err());
	}
	#[test]
	fn toggle_bit_i64() {
		assert_eq!(0b01i64.toggle_bit(1).ok(), Some(0b11));
		assert_eq!(0b01i64.toggle_bit(0).ok(), Some(0b00));
		assert!(0i64.toggle_bit(size_of::<i64>() * 8).is_err());
	}
	#[test]
	fn toggle_bit_isize() {
		assert_eq!(0b01isize.toggle_bit(1).ok(), Some(0b11));
		assert_eq!(0b01isize.toggle_bit(0).ok(), Some(0b00));
		assert!(0isize.toggle_bit(size_of::<isize>() * 8).is_err());
	}
}
