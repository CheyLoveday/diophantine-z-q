# Quartic polynomial tables

The filenames identify how the coefficients are written:

- **`fully-expanded.txt`** lists every nonzero monomial with its coefficient written out as a decimal integer.
- **`symbolic-coefficients.json`** also lists every nonzero monomial, but expresses some coefficients using the fixed integer `S = 3^(2^27)`. Those coefficients are exact; their full decimal digits are not written out. `S` is not an additional variable.

All variable counts include the input. Each download below is a byte-identical copy of the table in its linked verification package.

| Variables | Polynomial table | Coefficient format | Verification package |
| ---: | --- | --- | --- |
| 962 | [quartic-962-symbolic-coefficients.json](quartic-962-symbolic-coefficients.json) | Exact symbolic coefficients | [Version 6 guide](../docs/quartic-962/README.md), [package](quartic-962/) |
| 1,272 | [quartic-1272-symbolic-coefficients.json](quartic-1272-symbolic-coefficients.json) | Exact symbolic coefficients | [Version 5 package](quartic-1272/) |
| 4,973 | [quartic-4973-fully-expanded.txt](quartic-4973-fully-expanded.txt) | Fully written decimal integers | [Version 4 package](quartic-4973/) |
| 9,625 | [quartic-9625-fully-expanded.txt](quartic-9625-fully-expanded.txt) | Fully written decimal integers | [Version 3 package](quartic-9625/) |
| 12,504 | [quartic-12504-fully-expanded.txt](quartic-12504-fully-expanded.txt) | Fully written decimal integers | [Version 2 package](quartic-12504/) |

The 4,973-variable quartic is the smallest here with every coefficient written out in decimal. The current manuscript includes it and the 962-variable quartic, together with the original large construction in [construction/](../construction/README.md).

In a text table, each non-comment line contains the coefficient followed by repeated variable indices. For example, `-6 0 2 2` denotes `-6 X_0 X_2^2`. A line containing only a coefficient is the constant term. The JSON format is explained in the corresponding package guide.

The package directories retain their existing names because the source inventories, certificates and reproduction commands refer to those paths.
