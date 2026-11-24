"""fol-zfc-comb-lib's proof rules, where its ZF unit loads them: from the main repository."""

load("@fol_zfc//build:fol.bzl", _fol_group = "fol_group", _fol_library = "fol_library", _fol_proof = "fol_proof")

fol_group = _fol_group
fol_library = _fol_library
fol_proof = _fol_proof
