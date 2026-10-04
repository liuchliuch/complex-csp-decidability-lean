# PlanarHom dependency

The `PlanarHom` directory contains the proof-source dependency supplied with the
original formalization. It provides bit-machine constructions, exact field
encodings, interpolation, and the positive matrix counting-hardness results used
by ComplexCSP. These modules are built by the root Lake project.

The vendored Lean source is preserved byte for byte. Every included module is
in the production import closure; build outputs and historical audit material
are excluded. The original supplied snapshot had no license or public upstream
repository identifier, so this release does not assign it a new license.
