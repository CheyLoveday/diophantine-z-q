# Abelian-surface image and complement dimensions

## Scope

These are classical dimension deductions for the original abelian-variety objects and maps over the same algebraically closed characteristic-zero field k. They do not construct the original Lean image, kernel, complement, quasi-inverse, uniformization or source-world comparisons.

Both deductions have been independently checked as mathematical arguments under their stated geometric inputs. The original formal producers remain separate roadmap obligations.

## Image of a non-isogeny endomorphism

Let A/k be an abelian surface and f:A→A a nonzero integral endomorphism which is not finite and scheme-surjective. Suppose its actual abelian image is supplied as

A --q--> I --i--> A,

with q scheme-surjective, i a closed group inclusion, and f=i∘q. Then dim I=1.

First, Milne's isogeny characterization implies that f is not surjective: for an endomorphism the source and target dimensions are already equal, so surjectivity would imply isogeny. Hence the closed image is a proper irreducible closed subset of A. A chain of irreducible closed subsets in that image extends by the whole space of A; since dim A=2, the image dimension is at most one.

If dim I=0, finite type over k makes I finite and affine. Reducedness, irreducibility and algebraic closedness of k then give I≅Spec k. The composite f would be constant, and a group homomorphism constant on its source is constant at the identity. This would make f zero, a contradiction. Thus dim I=1.

The finite-type hypothesis is essential in this zero-dimensional argument. A finite irreducible topological space need not be a singleton: the spectrum of a discrete valuation ring has two points. No such shortcut is used here.

The chain comparison also keeps nilpotent thickenings out of the count: irreducible closed subsets correspond to the reduced integral closed subschemes used for Krull dimension. Milne's closed-point convention is reconciled with the full underlying scheme space through the lattice comparison in A.22.

This theorem assumes the actual image factorization. Existence and correct original-object realization of that factorization are not supplied by merely stating its dimension.

## Dimension of the Poincare complement

Let E/k be an actual one-dimensional abelian subvariety of the same A, with its given inclusion i:E→A. Apply Poincare reducibility to obtain an abelian complement F and a group inclusion j:F→A whose same sum map

s:E×F→A,  s(e,f)=i(e)+j(f),

is an isogeny. Then dim F=1.

The fibre-product universal property applied to dual-number points gives a linear isomorphism

T_(0,0)(E×F) ≅ T_0(E) ⊕ T_0(F).

These smooth group varieties are regular at their origins, so tangent dimensions equal geometric dimensions. Therefore dim(E×F)=dim E+dim F. Isogeny preserves dimension, hence 2=1+dim F and dim F=1.

The same s restricts to i on E×{0} and to j on {0}×F, by the actual group identity and the origin-preservation of i and j. These are identities of the given morphisms, not product coordinates on A.

The conclusion is only an isogeny from E×F to A. It does not assert A≅E×F, and it does not identify F with the connected kernel of the original f.

## Exact source locations

Milne, "Abelian Varieties", in *Arithmetic Geometry*, Springer-Verlag, 1986, pp. 103–150:

- Conventions, p. 103, and group-object definitions, p. 104: finite-type variety, regularity and group identity conventions.
- Corollary 2.4, p. 105: the group law of an abelian variety is commutative. This is what makes the sum map a homomorphism.
- Proposition 8.1, pp. 114–115: isogeny characterization and dimension equality for the sum-isogeny.
- Proposition 12.1, p. 122: Poincare complement and sum-isogeny.

The p. 104 sentence promising later commutativity is not its proof. The commutativity citation belongs to Corollary 2.4 on p. 105; p. 104 remains correct for the group identity used on the two axes.

Milne, *Algebraic Groups*, Cambridge Studies in Advanced Mathematics 170, Cambridge University Press, 2017:

- A.22, pp. 570–571: closed-point/full-scheme closed-set lattice comparison and surjectivity convention; the quoted comparison sentences occur on p. 571.
- A.47, p. 577: irreducible finite-type scheme dimension and its chain characterization.
- A.51–A.52, pp. 577–578: dual-number tangent space and equality of tangent/geometric dimensions at a regular k-point.
- Proposition 1.37, p. 18: smooth algebraic-group tangent dimension, as a cross-check.

Stacks Project:

- Lemma 33.20.2, Tag 06LH: a zero-dimensional scheme of finite type over a field is finite, https://stacks.math.columbia.edu/tag/06LH .
- Tag 01QO: closed-immersion characterization, https://stacks.math.columbia.edu/tag/01QO .

The read public copies are https://yhzhumath.github.io/Mordell2024/CS.pdf and https://www.jmilne.org/math/Books/iAG2017.pdf .

## Roadmap boundary

The classical dimension reductions are complete at these interfaces. Original image/complement objects, their group/field bindings, dimension conversions, positive-degree reverse morphisms and uniformization/rational-action joins must still be produced and verified for the formal development. These deductions introduce no new final quaternion-classification or Diophantine hypothesis and prove no whole Z-in-Q/H10 result by themselves.
