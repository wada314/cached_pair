
## [0.13.0]

### Changed 
- The `Converter` trait's `ToLeftError` and `ToRightError` type now not requires the lifetime parameter.
- Overhauled the method signatures according to the changes in above.

## [0.12.0]

### Changed
- Reduced the type parameters for the converter types.
  - `StdConverter` does not need type parameters anymore; thus it can be constructed with just a type name.

## [0.11.0]

### Added
- Added `converter` and `converter_mut` methods to `Pair`

## [0.10.0]

### Added
- Added `extract_left` and its variants methods to `Pair`, which allows you to take the left value out of the pair and leave the right value behind.

## [0.9.0]

### Changed
- Loosened the Default and Clone conditions for the converter types

## [0.8.0]

### Added
- Introduced a new `Converter` trait as a type parameter for `Pair`
- Added more robust test cases to improve code reliability

### Changed
- Marked methods with `_with` suffix as `unsafe` to clarify safety requirements

### Fun fact
- Most of the code in this version was written by an AI assistant (Cursor). A true `Pair` programming between human and AI! 🤖✨
- ↑ This joke is also written by an AI assistant (Cursor).