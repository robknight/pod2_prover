# POD2 Deduction Rules Implementation Status

## Currently Implemented Operations
- [x] `GtToNEq` (Code 8): Deduces `NEq(ak1, ak2)` from `Gt(ak1, ak2)`
- [x] `EntryGt` (Code 5): Deduces `Gt(ak1, ak2)` from value comparisons
- [x] `EntryEq` (Code 3): Deduces `Eq(ak1, ak2)` from equal values
- [x] `TransitiveEq` (Code 7): Deduces `Eq(ak1, ak4)` from transitive equality chain

## Pending Implementation
- [ ] `EntryNEq` (Code 4)
- [ ] `EntryLEq` (Code 6)
- [ ] `LtToNEq` (Code 9)
- [ ] `EntryContains` (Code 10)
- [ ] `EntrySintains` (Code 11)
- [ ] `RenameContains` (Code 12)
- [ ] `SumOf` (Code 13)
- [ ] `ProductOf` (Code 14)
- [ ] `MaxOf` (Code 15)

## Future POD2 Operations (Not Yet Supported)
These operations are planned but not yet implemented in POD2 itself:

- [ ] `SymmetricEq`: Deduces `Eq(ak2, ak1)` from `Equal(ak1, ak2)`
- [ ] `SymmetricNEq`: Deduces `NEq(ak2, ak1)` from `NotEqual(ak1, ak2)`
- [ ] `RenameSintains`: Deduces `Sintains(ak4, ak2)` from `Sintains(ak1, ak2)` and equality
- [ ] `TransitiveGt`: Deduces `Gt(ak1, ak4)` from transitive greater-than chain
- [ ] `TransitiveLEq`: Deduces `LEq(ak1, ak4)` from transitive less-than-or-equal chain
- [ ] `LEqToNEq`: Deduces `NEq(ak1, ak2)` from `LEq(ak1, ak2)`
