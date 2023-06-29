use std::collections::VecDeque;
use crate::{no_std_prelude::*, Word};
use alloy_primitives::{Address, I256, U256};

/// This type represents a Solidity value that has been decoded into rust. It
/// is broadly similar to `serde_json::Value` in that it is an enum of possible
/// types, and the user must inspect and disambiguate.
#[derive(Debug, Clone, PartialEq)]
pub enum DynSolValue {
    /// An address.
    Address(Address),
    /// A boolean.
    Bool(bool),
    /// A dynamic-length byte array.
    Bytes(Vec<u8>),
    /// A fixed-length byte string.
    FixedBytes(Word, usize),
    /// A signed integer.
    Int(I256, usize),
    /// An unsigned integer.
    Uint(U256, usize),
    /// A string.
    String(String),
    /// A tuple of values.
    Tuple(Vec<DynSolValue>),
    /// A dynamically-sized array of values.
    Array(Vec<DynSolValue>),
    /// A fixed-size array of values.
    FixedArray(Vec<DynSolValue>),
    /// A named struct, treated as a tuple with a name parameter.
    CustomStruct {
        /// The name of the struct.
        name: String,
        /// The struct's prop names, in declaration order.
        prop_names: Vec<String>,
        /// The inner types.
        tuple: Vec<DynSolValue>,
    },
    /// A user-defined value type.
    CustomValue {
        /// The name of the custom value type.
        name: String,
        /// The value itself.
        inner: Word,
    },
}

static ZEROS: [u8; 32] = [0; 32];

impl DynSolValue {
    /// The Solidity type name.
    pub fn sol_type_name(&self) -> String {
        match self {
            Self::Address(_) => "address".to_string(),
            Self::Bool(_) => "bool".to_string(),
            Self::Bytes(_) => "bytes".to_string(),
            Self::FixedBytes(_, size) => format!("bytes{}", size),
            Self::Int(_, size) => format!("int{}", size),
            Self::Uint(_, size) => format!("uint{}", size),
            Self::String(_) => "string".to_string(),
            Self::Tuple(_) => "tuple".to_string(),
            Self::Array(_) => "array".to_string(),
            Self::FixedArray(_) => "fixed_array".to_string(),
            Self::CustomStruct { name, .. } => name.clone(),
            Self::CustomValue { name, .. } => name.clone(),
        }
    }

    /// Fallible cast to a single word. Will succeed for any single-word type.
    pub fn as_word(&self) -> Option<Word> {
        match self {
            Self::Address(a) => Some(a.into_word()),
            Self::Bool(b) => Some({
                let mut buf = [0u8; 32];
                if *b {
                    buf[31] = 1;
                }
                buf.into()
            }),
            Self::FixedBytes(w, _) => Some(*w),
            Self::Int(w, _) => Some(w.to_be_bytes().into()),
            Self::Uint(u, _) => Some(u.to_be_bytes::<32>().into()),
            Self::CustomValue { inner, .. } => Some(*inner),
            _ => None,
        }
    }

    /// Fallible cast to the contents of a variant DynSolValue {.
    pub const fn as_address(&self) -> Option<Address> {
        match self {
            Self::Address(a) => Some(*a),
            _ => None,
        }
    }

    /// Fallible cast to the contents of a variant.
    pub const fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Fallible cast to the contents of a variant.
    pub fn as_bytes(&self) -> Option<&[u8]> {
        match self {
            Self::Bytes(b) => Some(b),
            _ => None,
        }
    }

    /// Fallible cast to the contents of a variant.
    pub const fn as_fixed_bytes(&self) -> Option<(&[u8], usize)> {
        match self {
            Self::FixedBytes(w, size) => Some((w.as_slice(), *size)),
            _ => None,
        }
    }

    /// Fallible cast to the contents of a variant.
    pub const fn as_int(&self) -> Option<(I256, usize)> {
        match self {
            Self::Int(w, size) => Some((*w, *size)),
            _ => None,
        }
    }

    /// Fallible cast to the contents of a variant.
    pub const fn as_uint(&self) -> Option<(U256, usize)> {
        match self {
            Self::Uint(u, size) => Some((*u, *size)),
            _ => None,
        }
    }

    /// Fallible cast to the contents of a variant.
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(s) => Some(s.as_str()),
            _ => None,
        }
    }

    /// Fallible cast to the contents of a variant.
    pub fn as_tuple(&self) -> Option<&[DynSolValue]> {
        match self {
            Self::Tuple(t) => Some(t.as_slice()),
            _ => None,
        }
    }

    /// Fallible cast to the contents of a variant.
    pub fn as_array(&self) -> Option<&[DynSolValue]> {
        match self {
            Self::Array(a) => Some(a.as_slice()),
            _ => None,
        }
    }

    /// Fallible cast to the contents of a variant.
    pub fn as_fixed_array(&self) -> Option<&[DynSolValue]> {
        match self {
            Self::FixedArray(a) => Some(a.as_slice()),
            _ => None,
        }
    }

    /// Fallible cast to the contents of a variant.
    pub fn as_custom_struct(&self) -> Option<(&str, &[String], &[DynSolValue])> {
        match self {
            Self::CustomStruct {
                name,
                prop_names,
                tuple,
            } => Some((name.as_str(), prop_names.as_slice(), tuple.as_slice())),
            _ => None,
        }
    }

    /// Fallible cast to the contents of a variant.
    pub fn as_custom_value(&self) -> Option<(&str, Word)> {
        match self {
            Self::CustomValue { name, inner } => Some((name.as_str(), *inner)),
            _ => None,
        }
    }

    /// Encodes the packed value and appends it to the end of a byte array.
    pub fn encode_packed_to(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Address(addr) => buf.extend_from_slice(addr.as_slice()),
            Self::Bool(b) => buf.push(*b as u8),
            Self::Bytes(bytes) => buf.extend_from_slice(bytes),
            Self::FixedBytes(word, size) => buf.extend_from_slice(&word.as_slice()[..*size]),
            Self::Int(num, size) => {
                let mut bytes = num.to_be_bytes::<32>();
                let start = 32 - *size;
                if num.is_negative() {
                    bytes[start] |= 0x80;
                } else {
                    bytes[start] &= 0x7f;
                }
                buf.extend_from_slice(&bytes[start..])
            }
            Self::Uint(num, size) => {
                buf.extend_from_slice(&num.to_be_bytes::<32>().as_slice()[(32 - *size)..])
            }
            Self::String(s) => buf.extend_from_slice(s.as_bytes()),
            Self::Tuple(inner)
            | Self::Array(inner)
            | Self::FixedArray(inner)
            | Self::CustomStruct { tuple: inner, .. } => {
                inner.iter().for_each(|v| v.encode_packed_to(buf))
            }
            Self::CustomValue { inner, .. } => buf.extend_from_slice(inner.as_slice()),
        }
    }

    #[inline]
    fn in_words(len: usize) -> u32 {
        ((len as u32) + 31) / 32
    }

    fn is_dynamic(&self) -> bool {
        match self {
            Self::Address(_)
            | Self::Bool(_)
            | Self::FixedBytes(_, _)
            | Self::Int(_, _)
            | Self::Uint(_, _)
            | Self::CustomValue { .. } => false,
            Self::Bytes(_)
            | Self::String(_)
            | Self::Array(_) => true,
            Self::FixedArray(inner) => inner[0].is_dynamic(),
            Self::CustomStruct{ tuple: inner, .. }
            | Self::Tuple(inner) => inner.iter().any(Self::is_dynamic),
        }
    }

    fn head_bytes(&self) -> u32 {
        match self {
            Self::Address(_)
            | Self::Bool(_)
            | Self::FixedBytes(_, _)
            | Self::Int(_, _)
            | Self::Uint(_, _)
            | Self::CustomValue { .. }
            | Self::Bytes(_)
            | Self::String(_)
            | Self::Array(_) => 32,
            Self::FixedArray(inner) => {
                if inner[0].is_dynamic() {
                    32
                } else {
                    inner.iter().map(|x| x.head_bytes()).sum()
                }
            }
            Self::Tuple(inner)
            | Self::CustomStruct { tuple: inner, .. } => {
                inner.iter().map(|x| x.head_bytes()).sum()
            }
        }
    }

    fn tail_bytes(&self) -> u32 {
        match self {
            Self::Address(_)
            | Self::Bool(_)
            | Self::FixedBytes(_, _)
            | Self::Int(_, _)
            | Self::Uint(_, _)
            | Self::CustomValue { .. } => 0,
            Self::Bytes(b) => 1 + Self::in_words(b.len()),
            Self::String(s) => 1 + Self::in_words(s.len()),
            Self::Array(x) => 1u32 + x.iter().map(Self::tail_bytes).sum::<u32>(),
            Self::FixedArray(inner) => {
                if inner[0].is_dynamic() {
                    inner.iter().map(|x| x.head_bytes() + x.tail_bytes()).sum()
                } else {
                    0
                }
            }
            Self::Tuple(inner)
            | Self::CustomStruct { tuple: inner, .. } => inner.iter().map(Self::tail_bytes).sum::<u32>()
        }
    }

    /// Encodes the value
    pub fn encode(&self) -> Vec<u8> {
        let quick_encode = self.quick_encode();
        if quick_encode.is_some() {
            return quick_encode.unwrap();
        }
        let head= self.head_bytes();
        // let tail = self.tail_bytes();
        let mut result = Vec::with_capacity((head + 32) as usize);
        let mut tail_pos = head;
        self.encode_to_inner(&mut result, &mut tail_pos);
        result
    }

    fn quick_encode(&self) -> Option<Vec<u8>> {
        match self {
            Self::Address(addr) => {
                let mut buf = Vec::with_capacity(32);
                buf.extend_from_slice(&ZEROS[20..]);
                buf.extend_from_slice(addr.as_slice());
                Some(buf)
            }
            Self::Bool(b) => {
                let mut buf = Vec::with_capacity(32);
                buf.extend_from_slice(&ZEROS[1..]);
                buf.push(*b as u8);
                Some(buf)
            }
            Self::Bytes(bytes) => {
                let mut buf = Vec::with_capacity(32 + Self::in_words(bytes.len()) as usize);
                Self::encode_u32(&mut buf, 1);
                Self::encode_u32(&mut buf, bytes.len() as u32);
                buf.extend_from_slice(&bytes[..]);
                if bytes.len() % 32 != 0 {
                    buf.extend_from_slice(&ZEROS[(bytes.len() % 32)..]);
                }
                Some(buf)
            }
            Self::String(s) => {
                let mut buf = Vec::with_capacity(32 + Self::in_words(s.len()) as usize);
                Self::encode_u32(&mut buf, 1);
                Self::encode_u32(&mut buf, s.len() as u32);
                buf.extend_from_slice(s.as_bytes());
                if s.len() % 32 != 0 {
                    buf.extend_from_slice(&ZEROS[(s.len() % 32)..]);
                }
                Some(buf)
            }
            Self::FixedBytes(word, _size) => {
                let mut buf = Vec::with_capacity(32);
                buf.extend_from_slice(&word.as_slice());
                Some(buf)
            }
            Self::Int(num, _size) => {
                let mut buf = Vec::with_capacity(32);
                let bytes = num.to_be_bytes::<32>();
                buf.extend_from_slice(&bytes);
                Some(buf)
            }
            Self::Uint(num, _size) => {
                let mut buf = Vec::with_capacity(32);
                buf.extend_from_slice(&num.to_be_bytes::<32>().as_slice());
                Some(buf)
            }
            Self::CustomValue { inner, .. } => {
                let mut buf = Vec::with_capacity(32);
                buf.extend_from_slice(inner.as_slice());
                Some(buf)
            }
            Self::Array(_)
            | Self::Tuple(_)
            | Self::FixedArray(_)
            | Self::CustomStruct { .. } => None
        }
    }

    fn head_encode_to<'myref, 'me: 'myref>(&'me self, buf: &mut Vec<u8>, tail_pos: &mut u32, tails: &mut VecDeque<&'myref DynSolValue>) {
        match self {
            Self::Address(addr) => {
                buf.extend_from_slice(&ZEROS[20..]);
                buf.extend_from_slice(addr.as_slice())
            }
            Self::Bool(b) => {
                buf.extend_from_slice(&ZEROS[1..]);
                buf.push(*b as u8)
            }
            Self::Bytes(_bytes) => {
                Self::encode_tail_pos(buf, tail_pos, self.tail_bytes());
                tails.push_back(self);
            }
            Self:: String(_s) => {
                Self::encode_tail_pos(buf, tail_pos, self.tail_bytes());
                tails.push_back(self);
            }
            Self:: Array(_) => {
                Self::encode_tail_pos(buf, tail_pos, self.tail_bytes());
                tails.push_back(self);
            }
            Self::FixedBytes(word, _size) => {
                buf.extend_from_slice(&word.as_slice())
            }
            Self::Int(num, _size) => {
                let bytes = num.to_be_bytes::<32>();
                buf.extend_from_slice(&bytes)
            }
            Self::Uint(num, _size) => {
                buf.extend_from_slice(&num.to_be_bytes::<32>().as_slice())
            }
            Self::Tuple(inner)
            | Self::FixedArray(inner)
            | Self::CustomStruct { tuple: inner, .. } => {
                inner.iter().for_each(|dv| dv.head_encode_to(buf, tail_pos, tails))
            }
            Self::CustomValue { inner, .. } => buf.extend_from_slice(inner.as_slice()),
        }
    }

    fn tail_encode_to<'myref, 'me: 'myref>(&'me self, buf: &mut Vec<u8>, tail_pos: &mut u32, tails: &mut VecDeque<&'myref DynSolValue>) {
        match self {
            Self::Bytes(bytes) => {
                Self::encode_u32(buf, bytes.len() as u32);
                buf.extend_from_slice(&bytes[..]);
                if bytes.len() % 32 != 0 {
                    buf.extend_from_slice(&ZEROS[(bytes.len() % 32)..]);
                }
            }
            Self:: String(s) => {
                Self::encode_u32(buf, s.len() as u32);
                buf.extend_from_slice(s.as_bytes());
                if s.len() % 32 != 0 {
                    buf.extend_from_slice(&ZEROS[(s.len() % 32)..]);
                }
            }
            Self:: Array(inner) => {
                Self::encode_u32(buf, inner.len() as u32);
                inner.iter().for_each(|dv| dv.head_encode_to(buf, tail_pos, tails));
            }
            Self::Tuple(inner)
            | Self::FixedArray(inner)
            | Self::CustomStruct { tuple: inner, .. } => {
                inner.iter().for_each(|dv| dv.tail_encode_to(buf, tail_pos, tails));
            }
            Self::Address(_)
            | Self::Bool(_)
            | Self::FixedBytes(_, _)
            | Self::Int(_, _)
            | Self::Uint(_, _)
            | Self::CustomValue { .. } => (), //shouldn't get here
        }
    }

    fn encode_to_inner(&self, buf: &mut Vec<u8>, tail_pos: &mut u32) {
        let mut tails: VecDeque<&DynSolValue> = VecDeque::with_capacity(0);
        self.head_encode_to(buf, tail_pos, &mut tails);
        let mut next_tail = tails.pop_front();
        while next_tail.is_some() {
            let tail = next_tail.unwrap();
            tail.tail_encode_to(buf, tail_pos, &mut tails);
            next_tail = tails.pop_front();
        }
    }

    #[inline]
    fn encode_tail_pos(buf: &mut Vec<u8>, tail_pos: &mut u32, tail_size: u32) {
        Self::encode_u32(buf, *tail_pos);
        *tail_pos += tail_size;
    }

    #[inline]
    fn encode_u32(buf: &mut Vec<u8>, v: u32) {
        buf.extend_from_slice(&ZEROS[4..]);
        buf.push((v >> 24) as u8);
        buf.push((v >> 16) as u8);
        buf.push((v >> 8) as u8);
        buf.push((v) as u8);
    }

    /// Encodes the value into a packed byte array.
    pub fn encode_packed(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.encode_packed_to(&mut buf);
        buf
    }
}

impl From<Address> for DynSolValue {
    #[inline]
    fn from(value: Address) -> Self {
        Self::Address(value)
    }
}

impl From<bool> for DynSolValue {
    #[inline]
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

impl From<Vec<u8>> for DynSolValue {
    #[inline]
    fn from(value: Vec<u8>) -> Self {
        Self::Bytes(value)
    }
}

impl From<String> for DynSolValue {
    #[inline]
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<Vec<DynSolValue>> for DynSolValue {
    #[inline]
    fn from(value: Vec<DynSolValue>) -> Self {
        Self::Array(value)
    }
}

impl<const N: usize> From<[DynSolValue; N]> for DynSolValue {
    #[inline]
    fn from(value: [DynSolValue; N]) -> Self {
        Self::FixedArray(value.to_vec())
    }
}

macro_rules! impl_from_int {
    ($($t:ty),+) => {$(
        impl From<$t> for DynSolValue {
            #[inline]
            fn from(value: $t) -> Self {
                const BITS: usize = <$t>::BITS as usize;
                const BYTES: usize = BITS / 8;
                const _: () = assert!(BYTES <= 32);

                let mut word = if value.is_negative() {
                    alloy_primitives::B256::repeat_byte(0xff)
                } else {
                    alloy_primitives::B256::ZERO
                };
                word[32 - BYTES..].copy_from_slice(&value.to_be_bytes());

                Self::Int(I256::from_be_bytes(word.0), BITS)
            }
        }
    )+};
}

impl_from_int!(i8, i16, i32, i64, isize, i128);

impl From<I256> for DynSolValue {
    #[inline]
    fn from(value: I256) -> Self {
        Self::Int(value, 256)
    }
}

macro_rules! impl_from_uint {
    ($($t:ty),+) => {$(
        impl From<$t> for DynSolValue {
            #[inline]
            fn from(value: $t) -> Self {
                Self::Uint(U256::from(value), <$t>::BITS as usize)
            }
        }
    )+};
}

impl_from_uint!(u8, u16, u32, u64, usize, u128);

impl From<U256> for DynSolValue {
    #[inline]
    fn from(value: U256) -> Self {
        Self::Uint(value, 256)
    }
}
