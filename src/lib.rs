use std::mem::size_of;

pub enum IndexError {
	UNDERSIZED,
}

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
	use super::{size_of, GetBit};
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
}
