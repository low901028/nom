//! Traits input types have to implement to work with nom combinators
use crate::error::{ErrorKind, ParseError};
use crate::internal::{Err, IResult, Needed};
use crate::lib::std::iter::{Copied, Enumerate};
use crate::lib::std::ops::{Range, RangeFrom, RangeFull, RangeTo};
use crate::lib::std::slice::Iter;
use crate::lib::std::str::from_utf8;
use crate::lib::std::str::CharIndices;
use crate::lib::std::str::Chars;
use crate::lib::std::str::FromStr;

#[cfg(feature = "alloc")]
use crate::lib::std::string::String;
#[cfg(feature = "alloc")]
use crate::lib::std::vec::Vec;

/// Abstract method to calculate the input length
pub trait InputLength {
  /// Calculates the input length, as indicated by its name,
  /// and the name of the trait itself
  fn input_len(&self) -> usize;
}

impl<'a, T> InputLength for &'a [T] {
  #[inline]
  fn input_len(&self) -> usize {
    self.len()
  }
}

impl<'a> InputLength for &'a str {
  #[inline]
  fn input_len(&self) -> usize {
    self.len()
  }
}

impl<'a> InputLength for (&'a [u8], usize) {
  #[inline]
  fn input_len(&self) -> usize {
    //println!("bit input length for ({:?}, {}):", self.0, self.1);
    //println!("-> {}", self.0.len() * 8 - self.1);
    self.0.len() * 8 - self.1
  }
}

/// Useful functions to calculate the offset between slices and show a hexdump of a slice
pub trait Offset {
  /// Offset between the first byte of self and the first byte of the argument
  fn offset(&self, second: &Self) -> usize;
}

impl Offset for [u8] {
  fn offset(&self, second: &Self) -> usize {
    let fst = self.as_ptr();
    let snd = second.as_ptr();

    snd as usize - fst as usize
  }
}

impl<'a> Offset for &'a [u8] {
  fn offset(&self, second: &Self) -> usize {
    let fst = self.as_ptr();
    let snd = second.as_ptr();

    snd as usize - fst as usize
  }
}

impl Offset for str {
  fn offset(&self, second: &Self) -> usize {
    let fst = self.as_ptr();
    let snd = second.as_ptr();

    snd as usize - fst as usize
  }
}

impl<'a> Offset for &'a str {
  fn offset(&self, second: &Self) -> usize {
    let fst = self.as_ptr();
    let snd = second.as_ptr();

    snd as usize - fst as usize
  }
}

/// Helper trait for types that can be viewed as a byte slice
pub trait AsBytes {
  /// Casts the input type to a byte slice
  fn as_bytes(&self) -> &[u8];
}

impl<'a> AsBytes for &'a str {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    (*self).as_bytes()
  }
}

impl AsBytes for str {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    self.as_ref()
  }
}

impl<'a> AsBytes for &'a [u8] {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    *self
  }
}

impl AsBytes for [u8] {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    self
  }
}

macro_rules! as_bytes_array_impls {
  ($($N:expr)+) => {
    $(
      impl<'a> AsBytes for &'a [u8; $N] {
        #[inline(always)]
        fn as_bytes(&self) -> &[u8] {
          *self
        }
      }

      impl AsBytes for [u8; $N] {
        #[inline(always)]
        fn as_bytes(&self) -> &[u8] {
          self
        }
      }
    )+
  };
}

as_bytes_array_impls! {
     0  1  2  3  4  5  6  7  8  9
    10 11 12 13 14 15 16 17 18 19
    20 21 22 23 24 25 26 27 28 29
    30 31 32
}

/// Transforms common types to a char for basic token parsing
pub trait AsChar {
  /// makes a char from self
  fn as_char(self) -> char;

  /// Tests that self is an alphabetic character
  ///
  /// Warning: for `&str` it recognizes alphabetic
  /// characters outside of the 52 ASCII letters
  fn is_alpha(self) -> bool;

  /// Tests that self is an alphabetic character
  /// or a decimal digit
  fn is_alphanum(self) -> bool;
  /// Tests that self is a decimal digit
  fn is_dec_digit(self) -> bool;
  /// Tests that self is an hex digit
  fn is_hex_digit(self) -> bool;
  /// Tests that self is an octal digit
  fn is_oct_digit(self) -> bool;
  /// Gets the len in bytes for self
  fn len(self) -> usize;
}

impl AsChar for u8 {
  #[inline]
  fn as_char(self) -> char {
    self as char
  }
  #[inline]
  fn is_alpha(self) -> bool {
    (self >= 0x41 && self <= 0x5A) || (self >= 0x61 && self <= 0x7A)
  }
  #[inline]
  fn is_alphanum(self) -> bool {
    self.is_alpha() || self.is_dec_digit()
  }
  #[inline]
  fn is_dec_digit(self) -> bool {
    self >= 0x30 && self <= 0x39
  }
  #[inline]
  fn is_hex_digit(self) -> bool {
    (self >= 0x30 && self <= 0x39)
      || (self >= 0x41 && self <= 0x46)
      || (self >= 0x61 && self <= 0x66)
  }
  #[inline]
  fn is_oct_digit(self) -> bool {
    self >= 0x30 && self <= 0x37
  }
  #[inline]
  fn len(self) -> usize {
    1
  }
}
impl<'a> AsChar for &'a u8 {
  #[inline]
  fn as_char(self) -> char {
    *self as char
  }
  #[inline]
  fn is_alpha(self) -> bool {
    (*self >= 0x41 && *self <= 0x5A) || (*self >= 0x61 && *self <= 0x7A)
  }
  #[inline]
  fn is_alphanum(self) -> bool {
    self.is_alpha() || self.is_dec_digit()
  }
  #[inline]
  fn is_dec_digit(self) -> bool {
    *self >= 0x30 && *self <= 0x39
  }
  #[inline]
  fn is_hex_digit(self) -> bool {
    (*self >= 0x30 && *self <= 0x39)
      || (*self >= 0x41 && *self <= 0x46)
      || (*self >= 0x61 && *self <= 0x66)
  }
  #[inline]
  fn is_oct_digit(self) -> bool {
    *self >= 0x30 && *self <= 0x37
  }
  #[inline]
  fn len(self) -> usize {
    1
  }
}

impl AsChar for char {
  #[inline]
  fn as_char(self) -> char {
    self
  }
  #[inline]
  fn is_alpha(self) -> bool {
    self.is_ascii_alphabetic()
  }
  #[inline]
  fn is_alphanum(self) -> bool {
    self.is_alpha() || self.is_dec_digit()
  }
  #[inline]
  fn is_dec_digit(self) -> bool {
    self.is_ascii_digit()
  }
  #[inline]
  fn is_hex_digit(self) -> bool {
    self.is_ascii_hexdigit()
  }
  #[inline]
  fn is_oct_digit(self) -> bool {
    self.is_digit(8)
  }
  #[inline]
  fn len(self) -> usize {
    self.len_utf8()
  }
}

impl<'a> AsChar for &'a char {
  #[inline]
  fn as_char(self) -> char {
    *self
  }
  #[inline]
  fn is_alpha(self) -> bool {
    self.is_ascii_alphabetic()
  }
  #[inline]
  fn is_alphanum(self) -> bool {
    self.is_alpha() || self.is_dec_digit()
  }
  #[inline]
  fn is_dec_digit(self) -> bool {
    self.is_ascii_digit()
  }
  #[inline]
  fn is_hex_digit(self) -> bool {
    self.is_ascii_hexdigit()
  }
  #[inline]
  fn is_oct_digit(self) -> bool {
    self.is_digit(8)
  }
  #[inline]
  fn len(self) -> usize {
    self.len_utf8()
  }
}

/// Abstracts common iteration operations on the input type
pub trait InputIter {
  /// The current input type is a sequence of that `Item` type.
  ///
  /// Example: `u8` for `&[u8]` or `char` for `&str`
  type Item;
  /// An iterator over the input type, producing the item and its position
  /// for use with [Slice]. If we're iterating over `&str`, the position
  /// corresponds to the byte index of the character
  type Iter: Iterator<Item = (usize, Self::Item)>;

  /// An iterator over the input type, producing the item
  type IterElem: Iterator<Item = Self::Item>;

  /// Returns an iterator over the elements and their byte offsets
  fn iter_indices(&self) -> Self::Iter;
  /// Returns an iterator over the elements
  fn iter_elements(&self) -> Self::IterElem;
  /// Finds the byte position of the element
  fn position<P>(&self, predicate: P) -> Option<usize>
  where
    P: Fn(Self::Item) -> bool;
  /// Get the byte offset from the element's position in the stream
  fn slice_index(&self, count: usize) -> Result<usize, Needed>;
}

/// Abstracts slicing operations
pub trait InputTake: Sized {
  /// Returns a slice of `count` bytes. panics if count > length
  fn take(&self, count: usize) -> Self;
  /// Split the stream at the `count` byte offset. panics if count > length
  fn take_split(&self, count: usize) -> (Self, Self);
}

impl<'a> InputIter for &'a [u8] {
  type Item = u8;
  type Iter = Enumerate<Self::IterElem>;
  type IterElem = Copied<Iter<'a, u8>>;

  #[inline]
  fn iter_indices(&self) -> Self::Iter {
    self.iter_elements().enumerate()
  }
  #[inline]
  fn iter_elements(&self) -> Self::IterElem {
    self.iter().copied()
  }
  #[inline]
  fn position<P>(&self, predicate: P) -> Option<usize>
  where
    P: Fn(Self::Item) -> bool,
  {
    self.iter().position(|b| predicate(*b))
  }
  #[inline]
  fn slice_index(&self, count: usize) -> Result<usize, Needed> {
    if self.len() >= count {
      Ok(count)
    } else {
      Err(Needed::new(count - self.len()))
    }
  }
}

impl<'a> InputTake for &'a [u8] {
  #[inline]
  fn take(&self, count: usize) -> Self {
    &self[0..count]
  }
  #[inline]
  fn take_split(&self, count: usize) -> (Self, Self) {
    let (prefix, suffix) = self.split_at(count);
    (suffix, prefix)
  }
}

impl<'a> InputIter for &'a str {
  type Item = char;
  type Iter = CharIndices<'a>;
  type IterElem = Chars<'a>;
  #[inline]
  fn iter_indices(&self) -> Self::Iter {
    self.char_indices()
  }
  #[inline]
  fn iter_elements(&self) -> Self::IterElem {
    self.chars()
  }
  fn position<P>(&self, predicate: P) -> Option<usize>
  where
    P: Fn(Self::Item) -> bool,
  {
    for (o, c) in self.char_indices() {
      if predicate(c) {
        return Some(o);
      }
    }
    None
  }
  #[inline]
  fn slice_index(&self, count: usize) -> Result<usize, Needed> {
    let mut cnt = 0;
    for (index, _) in self.char_indices() {
      if cnt == count {
        return Ok(index);
      }
      cnt += 1;
    }
    if cnt == count {
      return Ok(self.len());
    }
    Err(Needed::Unknown)
  }
}

impl<'a> InputTake for &'a str {
  #[inline]
  fn take(&self, count: usize) -> Self {
    &self[..count]
  }

  // return byte index
  #[inline]
  fn take_split(&self, count: usize) -> (Self, Self) {
    let (prefix, suffix) = self.split_at(count);
    (suffix, prefix)
  }
}

/// Dummy trait used for default implementations (currently only used for `InputTakeAtPosition` and `Compare`).
///
/// When implementing a custom input type, it is possible to use directly the
/// default implementation: If the input type implements `InputLength`, `InputIter`,
/// `InputTake` and `Clone`, you can implement `UnspecializedInput` and get
/// a default version of `InputTakeAtPosition` and `Compare`.
///
/// For performance reasons, you might want to write a custom implementation of
/// `InputTakeAtPosition` (like the one for `&[u8]`).
pub trait UnspecializedInput {}

/// Methods to take as much input as possible until the provided function returns true for the current element.
///
/// A large part of nom's basic parsers are built using this trait.
pub trait InputTakeAtPosition: Sized {
  /// The current input type is a sequence of that `Item` type.
  ///
  /// Example: `u8` for `&[u8]` or `char` for `&str`
  type Item;

  /// Looks for the first element of the input type for which the condition returns true,
  /// and returns the input up to this position.
  ///
  /// *streaming version*: If no element is found matching the condition, this will return `Incomplete`
  fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool;

  /// Looks for the first element of the input type for which the condition returns true
  /// and returns the input up to this position.
  ///
  /// Fails if the produced slice is empty.
  ///
  /// *streaming version*: If no element is found matching the condition, this will return `Incomplete`
  fn split_at_position1<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool;

  /// Looks for the first element of the input type for which the condition returns true,
  /// and returns the input up to this position.
  ///
  /// *complete version*: If no element is found matching the condition, this will return the whole input
  fn split_at_position_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool;

  /// Looks for the first element of the input type for which the condition returns true
  /// and returns the input up to this position.
  ///
  /// Fails if the produced slice is empty.
  ///
  /// *complete version*: If no element is found matching the condition, this will return the whole input
  fn split_at_position1_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool;
}

impl<T: InputLength + InputIter + InputTake + Clone + UnspecializedInput> InputTakeAtPosition
  for T
{
  type Item = <T as InputIter>::Item;

  fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.position(predicate) {
      Some(n) => Ok(self.take_split(n)),
      None => Err(Err::Incomplete(Needed::new(1))),
    }
  }

  fn split_at_position1<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.position(predicate) {
      Some(0) => Err(Err::Error(E::from_error_kind(self.clone(), e))),
      Some(n) => Ok(self.take_split(n)),
      None => Err(Err::Incomplete(Needed::new(1))),
    }
  }

  fn split_at_position_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.split_at_position(predicate) {
      Err(Err::Incomplete(_)) => Ok(self.take_split(self.input_len())),
      res => res,
    }
  }

  fn split_at_position1_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.split_at_position1(predicate, e) {
      Err(Err::Incomplete(_)) => {
        if self.input_len() == 0 {
          Err(Err::Error(E::from_error_kind(self.clone(), e)))
        } else {
          Ok(self.take_split(self.input_len()))
        }
      }
      res => res,
    }
  }
}

impl<'a> InputTakeAtPosition for &'a [u8] {
  type Item = u8;

  fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.iter().position(|c| predicate(*c)) {
      Some(i) => Ok(self.take_split(i)),
      None => Err(Err::Incomplete(Needed::new(1))),
    }
  }

  fn split_at_position1<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.iter().position(|c| predicate(*c)) {
      Some(0) => Err(Err::Error(E::from_error_kind(self, e))),
      Some(i) => Ok(self.take_split(i)),
      None => Err(Err::Incomplete(Needed::new(1))),
    }
  }

  fn split_at_position_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.iter().position(|c| predicate(*c)) {
      Some(i) => Ok(self.take_split(i)),
      None => Ok(self.take_split(self.input_len())),
    }
  }

  fn split_at_position1_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.iter().position(|c| predicate(*c)) {
      Some(0) => Err(Err::Error(E::from_error_kind(self, e))),
      Some(i) => Ok(self.take_split(i)),
      None => {
        if self.is_empty() {
          Err(Err::Error(E::from_error_kind(self, e)))
        } else {
          Ok(self.take_split(self.input_len()))
        }
      }
    }
  }
}

impl<'a> InputTakeAtPosition for &'a str {
  type Item = char;

  fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.find(predicate) {
      // find() returns a byte index that is already in the slice at a char boundary
      Some(i) => unsafe { Ok((self.get_unchecked(i..), self.get_unchecked(..i))) },
      None => Err(Err::Incomplete(Needed::new(1))),
    }
  }

  fn split_at_position1<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.find(predicate) {
      Some(0) => Err(Err::Error(E::from_error_kind(self, e))),
      // find() returns a byte index that is already in the slice at a char boundary
      Some(i) => unsafe { Ok((self.get_unchecked(i..), self.get_unchecked(..i))) },
      None => Err(Err::Incomplete(Needed::new(1))),
    }
  }

  fn split_at_position_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.find(predicate) {
      // find() returns a byte index that is already in the slice at a char boundary
      Some(i) => unsafe { Ok((self.get_unchecked(i..), self.get_unchecked(..i))) },
      // the end of slice is a char boundary
      None => unsafe {
        Ok((
          self.get_unchecked(self.len()..),
          self.get_unchecked(..self.len()),
        ))
      },
    }
  }

  fn split_at_position1_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.find(predicate) {
      Some(0) => Err(Err::Error(E::from_error_kind(self, e))),
      // find() returns a byte index that is already in the slice at a char boundary
      Some(i) => unsafe { Ok((self.get_unchecked(i..), self.get_unchecked(..i))) },
      None => {
        if self.is_empty() {
          Err(Err::Error(E::from_error_kind(self, e)))
        } else {
          // the end of slice is a char boundary
          unsafe {
            Ok((
              self.get_unchecked(self.len()..),
              self.get_unchecked(..self.len()),
            ))
          }
        }
      }
    }
  }
}

/// 比较两个内容是否成功： 主要是为了Compare trait的结果表示
/// Indicates whether a comparison was successful, an error, or
/// if more data was needed
#[derive(Debug, PartialEq)]
pub enum CompareResult {
  /// Comparison was successful
  /// 比较成功
  Ok,
  /// We need more data to be sure
  /// 结果比较不完整(需要更多些数据来验证)
  Incomplete,
  /// Comparison failed
  /// 比较结果失败
  Error,
}

/// 用于内容的比较： 结果见CompareResult
/// Abstracts comparison operations
pub trait Compare<T> {
  /// 自身的内容和指定的内容t比较是否完全匹配
  /// Compares self to another value for equality
  fn compare(&self, t: T) -> CompareResult;
  /// Compares self to another value for equality
  /// independently of the case.
  ///
  /// Warning: for `&str`, the comparison is done
  /// by lowercasing both strings and comparing
  /// the result. This is a temporary solution until
  /// a better one appears
  fn compare_no_case(&self, t: T) -> CompareResult;
}

/// 主要是为了比较进行字符串比较时都采用字母小写的方式进行比较
fn lowercase_byte(c: u8) -> u8 {
  match c {
    b'A'..=b'Z' => c - b'A' + b'a',
    _ => c,
  }
}

/// 用于当前内容和指定内容通过字节方式的比较:
/// 主要是获取比较第一次不同的位置：区分大小写
impl<'a, 'b> Compare<&'b [u8]> for &'a [u8] {
  #[inline(always)]
  fn compare(&self, t: &'b [u8]) -> CompareResult {
    // 通过zip将两个比较内容iterator进行对齐，并获取两者首次字节不匹配的位置
    // 一般来说是不存在的：self是全部内容，t则是self表示的全部内容的tag部分，正常情况pos=None；否则是error
    let pos = self.iter().zip(t.iter()).position(|(a, b)| a != b);

    match pos {
      Some(_) => CompareResult::Error, // 比较结果error
      None => {
        if self.len() >= t.len() {  // 需要确保self应该包含t内容
          CompareResult::Ok
        } else {                    // tag的内容和self全部内容比较需要更多的信息
          CompareResult::Incomplete
        }
      }
    }

    /*
    let len = self.len();
    let blen = t.len();
    let m = if len < blen { len } else { blen };
    let reduced = &self[..m];
    let b = &t[..m];

    if reduced != b {
      CompareResult::Error
    } else if m < blen {
      CompareResult::Incomplete
    } else {
      CompareResult::Ok
    }
    */
  }

  /// 比较当前内容和测试内容任意一个字节不同：不区分大小写
  /// 主要通过比较内容任意不同位置的字节(全部采用小写字母处理)
  #[inline(always)]
  fn compare_no_case(&self, t: &'b [u8]) -> CompareResult {
    if self
      .iter()
      .zip(t)
      .any(|(a, b)| lowercase_byte(*a) != lowercase_byte(*b))
    {
      CompareResult::Error
    } else if self.len() < t.len() {
      CompareResult::Incomplete
    } else {
      CompareResult::Ok
    }
  }
}

///
impl<
    T: InputLength + InputIter<Item = u8> + InputTake + UnspecializedInput,
    O: InputLength + InputIter<Item = u8> + InputTake,
  > Compare<O> for T
{
  #[inline(always)]
  fn compare(&self, t: O) -> CompareResult {
    let pos = self
      .iter_elements()
      .zip(t.iter_elements())
      .position(|(a, b)| a != b);

    match pos {
      Some(_) => CompareResult::Error,
      None => {
        if self.input_len() >= t.input_len() {
          CompareResult::Ok
        } else {
          CompareResult::Incomplete
        }
      }
    }
  }

  #[inline(always)]
  fn compare_no_case(&self, t: O) -> CompareResult {
    if self
      .iter_elements()
      .zip(t.iter_elements())
      .any(|(a, b)| lowercase_byte(a) != lowercase_byte(b))
    {
      CompareResult::Error
    } else if self.input_len() < t.input_len() {
      CompareResult::Incomplete
    } else {
      CompareResult::Ok
    }
  }
}

/// str和[u8]进行比较
impl<'a, 'b> Compare<&'b str> for &'a [u8] {
  #[inline(always)]
  fn compare(&self, t: &'b str) -> CompareResult {
    self.compare(AsBytes::as_bytes(t))
  }
  #[inline(always)]
  fn compare_no_case(&self, t: &'b str) -> CompareResult {
    self.compare_no_case(AsBytes::as_bytes(t))
  }
}

/// str和str进行比较
impl<'a, 'b> Compare<&'b str> for &'a str {
  #[inline(always)]
  fn compare(&self, t: &'b str) -> CompareResult {
    self.as_bytes().compare(t.as_bytes())
  }

  //FIXME: this version is too simple and does not use the current locale
  #[inline(always)]
  fn compare_no_case(&self, t: &'b str) -> CompareResult {
    let pos = self
      .chars()
      .zip(t.chars())
      .position(|(a, b)| a.to_lowercase().ne(b.to_lowercase()));

    match pos {
      Some(_) => CompareResult::Error,
      None => {
        if self.len() >= t.len() {
          CompareResult::Ok
        } else {
          CompareResult::Incomplete
        }
      }
    }
  }
}

/// [u8]和str比较
impl<'a, 'b> Compare<&'b [u8]> for &'a str {
  #[inline(always)]
  fn compare(&self, t: &'b [u8]) -> CompareResult {
    AsBytes::as_bytes(self).compare(t)
  }
  #[inline(always)]
  fn compare_no_case(&self, t: &'b [u8]) -> CompareResult {
    AsBytes::as_bytes(self).compare_no_case(t)
  }
}

/// 从当前内容中获取指定的token
/// Look for a token in self
pub trait FindToken<T> {
  /// Returns true if self contains the token
  fn find_token(&self, token: T) -> bool;
}

/// [u8]的实现查找指定的Token
/// 使用memchar查找当前内容包括的第一个匹配的字节
impl<'a> FindToken<u8> for &'a [u8] {
  fn find_token(&self, token: u8) -> bool {
    memchr::memchr(token, self).is_some()
  }
}

/// str的实现查找指定的token
impl<'a> FindToken<u8> for &'a str {
  fn find_token(&self, token: u8) -> bool {
    self.as_bytes().find_token(token)
  }
}

/// [u8]实现查找指定的token(以&u8格式)
impl<'a, 'b> FindToken<&'a u8> for &'b [u8] {
  fn find_token(&self, token: &u8) -> bool {
    self.find_token(*token)
  }
}

/// str实现查找指定的token(以&u8格式)
impl<'a, 'b> FindToken<&'a u8> for &'b str {
  fn find_token(&self, token: &u8) -> bool {
    self.as_bytes().find_token(token)
  }
}

/// [u8]实现查找指定的token(以char格式)
impl<'a> FindToken<char> for &'a [u8] {
  fn find_token(&self, token: char) -> bool {
    self.iter().any(|i| *i == token as u8)
  }
}

/// str实现查找指定的token(以char格式)
impl<'a> FindToken<char> for &'a str {
  fn find_token(&self, token: char) -> bool {
    self.chars().any(|i| i == token)
  }
}

/// [char]实现查找指定的token(以char格式)
impl<'a> FindToken<char> for &'a [char] {
  fn find_token(&self, token: char) -> bool {
    self.iter().any(|i| *i == token)
  }
}

/// [u8]实现查找指定的token(以&char格式)
impl<'a, 'b> FindToken<&'a char> for &'b [char] {
  fn find_token(&self, token: &char) -> bool {
    self.find_token(*token)
  }
}

/// 从当前内容查找指定的子串
/// Look for a substring in self
pub trait FindSubstring<T> {
  /// 存在符合要求字串的字节位置
  /// Returns the byte position of the substring if it is found
  fn find_substring(&self, substr: T) -> Option<usize>;
}

/// &[u8]实现查找指定子串(以&[u8])
impl<'a, 'b> FindSubstring<&'b [u8]> for &'a [u8] {
  fn find_substring(&self, substr: &'b [u8]) -> Option<usize> {
    if substr.len() > self.len() { // 当子串长度超过被查找的内容 是没有符合要求的子串存在
      return None;
    }

    // ？？？将需要查找的子串进行拆分两部分： 首字节和其余部分；
    // 能够通过首字节快速验证进行当前查找内容是否需要完全匹配所有的子串内容
    let (&substr_first, substr_rest) = match substr.split_first() { // split子串的第一个元素和剩余其他元素
      Some(split) => split,
      // an empty substring is found at position 0
      // This matches the behavior of str.find("").
      None => return Some(0), // 默认情况空子串认为位置=0
    };

    // case-1： 当只有首字节部分时
    if substr_rest.is_empty() { // 当查找的子串只包括一个字节，则直接通过memchr::memchr对被查找的内容(字节切片)进行查找
      return memchr::memchr(substr_first, self);
    }

    // case-2: 包含其余部分子串内容
    // 记录查找子串的首字节在被查找内容的位置； 默认从0开始
    let mut offset = 0;
    // 将被查找内容去掉和子串剩余其他部分的长度： &self[..self.len() - substr_rest.len()]
    // 在子串首字节和&self[..self.len() - substr_rest.len()]进行比较 是否存在
    let haystack = &self[..self.len() - substr_rest.len()];

    // 通过移动offset获取&self[..self.len() - substr_rest.len()]中内容，是否存在子串首字节；
    // 若是存在的话， 在比较最后匹配的position直到子串剩余部分内容长度是否和子串其他部分内容匹配； 那么最后的匹配位置则就是我们需要的位置
    while let Some(position) = memchr::memchr(substr_first, &haystack[offset..]) {
      offset += position;   // 不停迭代变换满足子串首字节的新位置offset
      let next_offset = offset + 1; // 获取最新子串首字节匹配位置position下一个位置
      if &self[next_offset..][..substr_rest.len()] == substr_rest { // 判断从最新匹配子串首字节位置开始直至长度=substr_rest.len()这段内容和子串其他部分是否匹配
        return Some(offset);  // 返回满足需要最新匹配位置
      }

      offset = next_offset; // 不停移动offset直到最后一个满足：匹配子串首字节的位置position结束
    }

    None
  }
}

impl<'a, 'b> FindSubstring<&'b str> for &'a [u8] {
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.find_substring(AsBytes::as_bytes(substr))
  }
}

impl<'a, 'b> FindSubstring<&'b str> for &'a str {
  //returns byte index
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.find(substr)
  }
}

/// 集成str的parse
/// Used to integrate `str`'s `parse()` method
pub trait ParseTo<R> {
  // 是通过parse()来完成解析操作；会将字节切片转为str在调用parse()
  /// Succeeds if `parse()` succeeded. The byte slice implementation
  /// will first convert it to a `&str`, then apply the `parse()` function
  fn parse_to(&self) -> Option<R>;
}

/// &[u8]实现ParseTo trait
impl<'a, R: FromStr> ParseTo<R> for &'a [u8] {
  fn parse_to(&self) -> Option<R> {
    // 将[u8]采用utf8格式编码转为str再调用parse()
    from_utf8(self).ok().and_then(|s| s.parse().ok())
  }
}

/// &str实现ParseTo trait: 直接调用parse()来完成
impl<'a, R: FromStr> ParseTo<R> for &'a str {
  fn parse_to(&self) -> Option<R> {
    self.parse().ok()
  }
}

/// 支持切片使用range，也是基于Index来完成的
/// Slicing operations using ranges.
///
/// This trait is loosely based on
/// `Index`, but can actually return
/// something else than a `&[T]` or `&str`
pub trait Slice<R> {
  /// Slices self according to the range argument
  fn slice(&self, range: R) -> Self;
}

/// 定义声明宏：获取切片
/// fn slice(&self, range: T) -> Self {
///       &self[range]
/// }
macro_rules! impl_fn_slice {
  ( $ty:ty ) => {
    fn slice(&self, range: $ty) -> Self {
      &self[range]
    }
  };
}

/// 声明宏：
/// case-1:
/// impl <'a, T> Slice<T> for &'a [T] {
///   impl_fn_slice(T);
///}
/// case-2:
/// impl <'a> Slice<T> for &'a T {
///    impl_fn_slice(T);
/// }
///
macro_rules! slice_range_impl {
  ( [ $for_type:ident ], $ty:ty ) => {
    impl<'a, $for_type> Slice<$ty> for &'a [$for_type] {
      impl_fn_slice!($ty);
    }
  };
  ( $for_type:ty, $ty:ty ) => {
    impl<'a> Slice<$ty> for &'a $for_type {
      impl_fn_slice!($ty);
    }
  };
}

macro_rules! slice_ranges_impl {
  ( [ $for_type:ident ] ) => {
    slice_range_impl! {[$for_type], Range<usize>}
    slice_range_impl! {[$for_type], RangeTo<usize>}
    slice_range_impl! {[$for_type], RangeFrom<usize>}
    slice_range_impl! {[$for_type], RangeFull}
  };
  ( $for_type:ty ) => {
    slice_range_impl! {$for_type, Range<usize>}
    slice_range_impl! {$for_type, RangeTo<usize>}
    slice_range_impl! {$for_type, RangeFrom<usize>}
    slice_range_impl! {$for_type, RangeFull}
  };
}

// str 和 T类型
slice_ranges_impl! {str}
slice_ranges_impl! {[T]}

macro_rules! array_impls {
  ($($N:expr)+) => {
    $(
      impl InputLength for [u8; $N] {
        #[inline]
        fn input_len(&self) -> usize {
          self.len()
        }
      }

      impl<'a> InputLength for &'a [u8; $N] {
        #[inline]
        fn input_len(&self) -> usize {
          self.len()
        }
      }

      impl<'a> InputIter for &'a [u8; $N] {
        type Item = u8;
        type Iter = Enumerate<Self::IterElem>;
        type IterElem = Copied<Iter<'a, u8>>;

        fn iter_indices(&self) -> Self::Iter {
          (&self[..]).iter_indices()
        }

        fn iter_elements(&self) -> Self::IterElem {
          (&self[..]).iter_elements()
        }

        fn position<P>(&self, predicate: P) -> Option<usize>
          where P: Fn(Self::Item) -> bool {
          (&self[..]).position(predicate)
        }

        fn slice_index(&self, count: usize) -> Result<usize, Needed> {
          (&self[..]).slice_index(count)
        }
      }

      impl<'a> Compare<[u8; $N]> for &'a [u8] {
        #[inline(always)]
        fn compare(&self, t: [u8; $N]) -> CompareResult {
          self.compare(&t[..])
        }

        #[inline(always)]
        fn compare_no_case(&self, t: [u8;$N]) -> CompareResult {
          self.compare_no_case(&t[..])
        }
      }

      impl<'a,'b> Compare<&'b [u8; $N]> for &'a [u8] {
        #[inline(always)]
        fn compare(&self, t: &'b [u8; $N]) -> CompareResult {
          self.compare(&t[..])
        }

        #[inline(always)]
        fn compare_no_case(&self, t: &'b [u8;$N]) -> CompareResult {
          self.compare_no_case(&t[..])
        }
      }

      impl FindToken<u8> for [u8; $N] {
        fn find_token(&self, token: u8) -> bool {
          memchr::memchr(token, &self[..]).is_some()
        }
      }

      impl<'a> FindToken<&'a u8> for [u8; $N] {
        fn find_token(&self, token: &u8) -> bool {
          self.find_token(*token)
        }
      }
    )+
  };
}

array_impls! {
     0  1  2  3  4  5  6  7  8  9
    10 11 12 13 14 15 16 17 18 19
    20 21 22 23 24 25 26 27 28 29
    30 31 32
}

/// Abstracts something which can extend an `Extend`.
/// Used to build modified input slices in `escaped_transform`
pub trait ExtendInto {
  /// The current input type is a sequence of that `Item` type.
  ///
  /// Example: `u8` for `&[u8]` or `char` for `&str`
  type Item;

  /// The type that will be produced
  type Extender;

  /// Create a new `Extend` of the correct type
  fn new_builder(&self) -> Self::Extender;
  /// Accumulate the input into an accumulator
  fn extend_into(&self, acc: &mut Self::Extender);
}

#[cfg(feature = "alloc")]
impl ExtendInto for [u8] {
  type Item = u8;
  type Extender = Vec<u8>;

  #[inline]
  fn new_builder(&self) -> Vec<u8> {
    Vec::new()
  }
  #[inline]
  fn extend_into(&self, acc: &mut Vec<u8>) {
    acc.extend(self.iter().cloned());
  }
}

#[cfg(feature = "alloc")]
impl ExtendInto for &[u8] {
  type Item = u8;
  type Extender = Vec<u8>;

  #[inline]
  fn new_builder(&self) -> Vec<u8> {
    Vec::new()
  }
  #[inline]
  fn extend_into(&self, acc: &mut Vec<u8>) {
    acc.extend_from_slice(self);
  }
}

#[cfg(feature = "alloc")]
impl ExtendInto for str {
  type Item = char;
  type Extender = String;

  #[inline]
  fn new_builder(&self) -> String {
    String::new()
  }
  #[inline]
  fn extend_into(&self, acc: &mut String) {
    acc.push_str(self);
  }
}

#[cfg(feature = "alloc")]
impl ExtendInto for &str {
  type Item = char;
  type Extender = String;

  #[inline]
  fn new_builder(&self) -> String {
    String::new()
  }
  #[inline]
  fn extend_into(&self, acc: &mut String) {
    acc.push_str(self);
  }
}

#[cfg(feature = "alloc")]
impl ExtendInto for char {
  type Item = char;
  type Extender = String;

  #[inline]
  fn new_builder(&self) -> String {
    String::new()
  }
  #[inline]
  fn extend_into(&self, acc: &mut String) {
    acc.push(*self);
  }
}

/// Helper trait to convert numbers to usize.
///
/// By default, usize implements `From<u8>` and `From<u16>` but not
/// `From<u32>` and `From<u64>` because that would be invalid on some
/// platforms. This trait implements the conversion for platforms
/// with 32 and 64 bits pointer platforms
pub trait ToUsize {
  /// converts self to usize
  fn to_usize(&self) -> usize;
}

impl ToUsize for u8 {
  #[inline]
  fn to_usize(&self) -> usize {
    *self as usize
  }
}

impl ToUsize for u16 {
  #[inline]
  fn to_usize(&self) -> usize {
    *self as usize
  }
}

impl ToUsize for usize {
  #[inline]
  fn to_usize(&self) -> usize {
    *self
  }
}

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
impl ToUsize for u32 {
  #[inline]
  fn to_usize(&self) -> usize {
    *self as usize
  }
}

#[cfg(target_pointer_width = "64")]
impl ToUsize for u64 {
  #[inline]
  fn to_usize(&self) -> usize {
    *self as usize
  }
}

/// Equivalent From implementation to avoid orphan rules in bits parsers
pub trait ErrorConvert<E> {
  /// Transform to another error type
  fn convert(self) -> E;
}

impl<I> ErrorConvert<(I, ErrorKind)> for ((I, usize), ErrorKind) {
  fn convert(self) -> (I, ErrorKind) {
    ((self.0).0, self.1)
  }
}

impl<I> ErrorConvert<((I, usize), ErrorKind)> for (I, ErrorKind) {
  fn convert(self) -> ((I, usize), ErrorKind) {
    ((self.0, 0), self.1)
  }
}

use crate::error;
impl<I> ErrorConvert<error::Error<I>> for error::Error<(I, usize)> {
  fn convert(self) -> error::Error<I> {
    error::Error {
      input: self.input.0,
      code: self.code,
    }
  }
}

impl<I> ErrorConvert<error::Error<(I, usize)>> for error::Error<I> {
  fn convert(self) -> error::Error<(I, usize)> {
    error::Error {
      input: (self.input, 0),
      code: self.code,
    }
  }
}

#[cfg(feature = "alloc")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
impl<I> ErrorConvert<error::VerboseError<I>> for error::VerboseError<(I, usize)> {
  fn convert(self) -> error::VerboseError<I> {
    error::VerboseError {
      errors: self.errors.into_iter().map(|(i, e)| (i.0, e)).collect(),
    }
  }
}

#[cfg(feature = "alloc")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
impl<I> ErrorConvert<error::VerboseError<(I, usize)>> for error::VerboseError<I> {
  fn convert(self) -> error::VerboseError<(I, usize)> {
    error::VerboseError {
      errors: self.errors.into_iter().map(|(i, e)| ((i, 0), e)).collect(),
    }
  }
}

#[cfg(feature = "std")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "std")))]
/// Helper trait to show a byte slice as a hex dump
pub trait HexDisplay {
  /// Converts the value of `self` to a hex dump, returning the owned
  /// `String`.
  fn to_hex(&self, chunk_size: usize) -> String;

  /// Converts the value of `self` to a hex dump beginning at `from` address, returning the owned
  /// `String`.
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String;
}

#[cfg(feature = "std")]
static CHARS: &[u8] = b"0123456789abcdef";

#[cfg(feature = "std")]
impl HexDisplay for [u8] {
  #[allow(unused_variables)]
  fn to_hex(&self, chunk_size: usize) -> String {
    self.to_hex_from(chunk_size, 0)
  }

  #[allow(unused_variables)]
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String {
    let mut v = Vec::with_capacity(self.len() * 3);
    let mut i = from;
    for chunk in self.chunks(chunk_size) {
      let s = format!("{:08x}", i);
      for &ch in s.as_bytes().iter() {
        v.push(ch);
      }
      v.push(b'\t');

      i += chunk_size;

      for &byte in chunk {
        v.push(CHARS[(byte >> 4) as usize]);
        v.push(CHARS[(byte & 0xf) as usize]);
        v.push(b' ');
      }
      if chunk_size > chunk.len() {
        for j in 0..(chunk_size - chunk.len()) {
          v.push(b' ');
          v.push(b' ');
          v.push(b' ');
        }
      }
      v.push(b'\t');

      for &byte in chunk {
        if (byte >= 32 && byte <= 126) || byte >= 128 {
          v.push(byte);
        } else {
          v.push(b'.');
        }
      }
      v.push(b'\n');
    }

    String::from_utf8_lossy(&v[..]).into_owned()
  }
}

#[cfg(feature = "std")]
impl HexDisplay for str {
  #[allow(unused_variables)]
  fn to_hex(&self, chunk_size: usize) -> String {
    self.to_hex_from(chunk_size, 0)
  }

  #[allow(unused_variables)]
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String {
    self.as_bytes().to_hex_from(chunk_size, from)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_offset_u8() {
    let s = b"abcd123";
    let a = &s[..];
    let b = &a[2..];
    let c = &a[..4];
    let d = &a[3..5];
    assert_eq!(a.offset(b), 2);
    assert_eq!(a.offset(c), 0);
    assert_eq!(a.offset(d), 3);
  }

  #[test]
  fn test_offset_str() {
    let s = "abcřèÂßÇd123";
    let a = &s[..];
    let b = &a[7..];
    let c = &a[..5];
    let d = &a[5..9];
    assert_eq!(a.offset(b), 7);
    assert_eq!(a.offset(c), 0);
    assert_eq!(a.offset(d), 5);
  }
}
