use std::mem::size_of;

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
