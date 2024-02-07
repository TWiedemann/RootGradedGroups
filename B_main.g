### First file to load.
### This file contains the basic setup for the commutative ring R,
### the R-module M, the free modules F_pos and F_neg,
### the R-module V = M + F_pos + F_neg,
### the quadratic form q: M -> R (and its extension qExt: V -> R)
### and its linearisation f: M x M -> R.

n := 4; # rank of the root system B_n

# ---- The ring R ----
# For the purposes of our computations, we can assume
# that R is the polynomial ring over the integers with
# infinitely many indeterminates. Any computation in R
# is valid in an arbitrary commutative ring.
R := PolynomialRing(Integers);

# ---- The free modules F_pos and F_neg ----
# F_pos and F_neg are free R-modules of rank n.
# Elements of F_pos and F_neg are represented
# by a coefficient list of length n. The list
# entries are polynomials of the Integers.
# The generators of both F_pos and F_neg are called
# b_1 = b[1], ..., b_n = b[n]. We will distinguish between F_pos
# and F_neg when we embed them into a larger module V.
b := []; # List of basis vectors for F_pos and F_neg
for i in [1..n] do
	b[i] := [];
	for j in [1..n] do
		if j = i then
			Add(b[i], Identity(R)); # 1
		else
			Add(b[i], Zero(R)); # 0
		fi;
	od;
od;
# Zero vector in F_pos and F_neg
zeroFree := NullMat(1, n, R)[1];
# --------

# ---- The module M ---
# M represents an arbitrary R-module, called the "abstract module".
# All computations in M involve at most a finite
# number m of distinct elements of M. Thus,
# for the sake of computations, we can assume
# that M is the free module of rank m. Elements of
# M are represented by coefficent lists of length m.
# The variable name for m is "rank".
# The generators of M are called v_1 = v[1], ..., v_rank = v[rank].
# The generator v[rank] represents an element u of the radical
# (i.e. q(u) = 0, f(v, u) = 0 for all v).
# Further, v[rank-1] is used in the functions funcsAreEqual. It represents
# an arbitrary module element which is only used for testing equality of functions.
# Hence v[rank-1] SHOULD NOT BE USED outside of funcsAreEqual.
# Thus in practice, there are rank-2 "freely usable" generators.
rank := 4; 
v := []; # List of "basis" vectors for M
for i in [1..rank] do
	v[i] := [];
	for j in [1..rank] do
		if j = i then
			Add(v[i], Identity(R)); # 1
		else
			Add(v[i], Zero(R)); # 0
		fi;
	od;
od;
# Zero vector in M
zeroM := NullMat(1, rank, R)[1];
# Names of the "basis" vectors (for printing f(v, w) and q(v))
vNames := [ "u1", "u2", "u3", "u_rad" ];
# --------

# ---- The module V ----
# We put V := M + F_pos + F_neg (direct sum).
# Elements of V are represented by lists
# [ mpart, pospart, negpart ]
# where mpart, pospart, negpart are elements
# of M, F_pos and F_neg, respectively.
# Generators of V:
vEmbed := List(v, x -> [ x, zeroFree, zeroFree ]); # vEmbed[1], ..., vEmbed[rank]
bPos := List(b, x -> [ zeroM, x, zeroFree ]); # bPos[1], ..., bPos[n]
bNeg := List(b, x -> [ zeroM, zeroFree, x ]); # bNeg[1], ..., bNeg[n]
# -------

# ---- q and f ----
# q: M -> R is an arbitrary quadratic form on M and
# f: M x M -> R, (x, y) -> q(x+y) - q(x) - q(y)
# is the associated bilinear form.
# For each basis vector v of M, we fix an indeterminate in R
# which represents q(v). For each pair of distinct basis
# vectors {v, w} of M, we fix an indeterminate which
# represents f(v, w) = f(w, v). Using the relations
# (1) q(a*v) = a^2 v for a \in R, v \in M,
# (2) q(v+w) = q(v) + q(w) + f(v, w) for v, w \in M,
# (3) f(v, v) = 2 q(v) for v \in M,
# we can decompose f(v, w) and q(v) as linear combinations
# of the indeterminates for all v, w \in M
qIndet := []; # list of indeterminates q(v_i)
fIndet := NullMat(rank, rank, Integers); # list of indeterminates f(v_i, v_j)

for i in [1..rank-1] do
	name := Concatenation("q(", vNames[i], ")");
	Add(qIndet, X(Integers, name));
	for j in [i..rank-1] do
		if i = j then
			fIndet[i][j] := fail; # no indeterminate f(v, v)
		else
			name := Concatenation("f(", vNames[i], ", ", vNames[j], ")");
			fIndet[i][j] := X(Integers, name);
			fIndet[j][i] := fIndet[i][j]; # f is symmetric
		fi;
	od;
od;

# The quadratic form on M
# q(\sum_i a_i v_i) = \sum_i a_i^2 q(v_i) + \sum_{i<j} a_i a_j f(v_i, v_j)
# (because of relations (1) and (2)).
# The last indeterminate v_rank is ignored because it is assumed to lie in the radical.
q := function(mpart)
	local sum, i, j;
	sum := 0;
	for i in [1..rank-1] do
		sum := sum + mpart[i]^2 * qIndet[i];
		for j in [i+1..rank-1] do
			sum := sum + mpart[i] * mpart[j] * fIndet[i][j];
		od;
	od;
	return sum;
end;

# The extension of q to V.
# Each pair (bPos[i], bNeg[i]) is (by definition) a hyperbolic pair,
# i.e. f(bPos[i], bNeg[i]) = 1, q(bPos[i]) = 0 = q(bNeg[i]) and
# { bPos[i], bNeg[i] } spans an orthogonal direct sumand of V.
qExt := function(modelement)
	local mpart, pospart, negpart, sum, i;
	mpart := modelement[1];
	pospart := modelement[2];
	negpart := modelement[3];
	sum := q(mpart);
	for i in [1..n] do
		sum := sum + pospart[i]*negpart[i];
	od;
	return sum;
end;

# Linearisation of q (on M):
# f(\sum_i a_i v_i, \sum_j b_j w_j) = sum_{i,j} a_i b_j f(v_i, w_j)
# where f(v, v) = 2 q(v)
# The last indeterminate v_rank is ignored because it is assumed to lie in the radical.
f := function(mpart1, mpart2)
	local sum, i, j;
	sum := 0;
	for i in [1..rank-1] do
		for j in [1..rank-1] do
			if i = j then
				sum := sum + 2 * mpart1[i] * mpart2[j] * qIndet[i];
			else
				sum := sum + mpart1[i] * mpart2[j] * fIndet[i][j];
			fi;
		od;
	od;
	return sum;
end;

# Linearisation of qExt (on V)
# Lazy implementation, but runtime is no problem anyway
fExt := function(modEl1, modEl2)
	return qExt(modEl1+modEl2) - qExt(modEl1) - qExt(modEl2);
end;

# ---- Auxiliary functions -----

# Returns \sigma_u(v) where \sigma_u is the reflection along u^\perp
refl := function(u, v)
	return v - q(u)^-1 * f(u, v) * u;
end;

# returns true if i "lies between j and k", otherwise false
between := function(i, j, k)
	return (j < i and i < k) or (k < i and i < j);
end;

# returns -1 if bool = true, otherwise 1
dminus := function(bool)
	if bool then return -1;
	else return 1; fi;
end;

# --------
