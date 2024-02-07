### First file to load.
### This file contains the basic setup for constructing a BC_n-graded group.

## We construct a BC_n-graded group EU(q) from the following data:
# - An associative ring R with an involution x -> x'. It comes with a subgroup R_0 of the fixed points of the involution, but R_0 does not appear in the computations.
# - A right module M over R
# - A pseudo-quadratic form q: M -> R with respect to the involution
# - An associated skew-hermitian form f: M x M -> R
# We represent R by a free associative ring on symbols x_1, ..., x_(ring_rank), y_1, ..., y_(ring_rank), { f(v_i, v_j) | 1 <= i, j <= n }.
# We define an involution on R by declaring x_i' := y_i, y_i' := x_i' and f(v_i, v_j)' := -f(v_j, v_i).
# Elements of M are represented by lists [ a_1, ..., a_r ] which represent the module element \sum_i v_i a_i where v_1, ..., v_r are "free symbols" and r = mod_rank.
# The pseudo-quadratic form q does not appear in the computations, so we do not have to define it.
# The group EU(q) consists of automorphisms of a module V which is the direct sum M + F_pos + F_neg. Here F_pos and F_neg are free modules of rank n.
# The medium-length root groups are parametrised by R.
# The short root groups are parametrised by T := { (u, t) | u \in M, t \in R, q(u) = t mod R_0 }. We will, however, define the root homomorphisms on all of M x R. Elements (u, t) \in T have the additional property that f(u, u) = t - t'. Whenever we perform computations involving an element (v_i, t) \in T, we can thus replace every instance of f(v_i, v_i) that appears in our computations by t - t'. Since, in fact, T = { (u, t) \in M x R | f(u, u) = t - t' }, this procedure is enough for our computations.

# ---- Global variables ----

n := 4; # rank of the root system BC_n
ring_rank := 4; # Number of independent elements of the ring
mod_rank := 4; # Number of independent elements of the abstract module

# ------------------------

# ---- Indeterminate names ----

modIndetNames := [];
for i in [1..mod_rank] do # [ v_1, ..., v_(ring_rank) ]
	Add(modIndetNames, Concatenation("v", String(i)));
od;
ringIndetNames := [];
for i in [1..ring_rank] do # [x_1, ..., x_(ring_rank)]
	Add(ringIndetNames, Concatenation("x", String(i)));
od;
for i in [1..ring_rank] do # [x_1', ..., x_(ring_rank)'] (Involution)
	Add(ringIndetNames, Concatenation("x", String(i), "'"));
od;
for i in [1..mod_rank] do # [f(v_i, v_j) | 1 <= i,j <= mod_rank ]
	for j in [1..mod_rank] do
		name := Concatenation("f(", modIndetNames[i], ",", modIndetNames[j], ")");
		Add(ringIndetNames, name);
	od;
od;

# -------------------------

# ---- The ring R ----

## Basic setup
Mon := FreeGroup(ringIndetNames); # Monoid of indeterminates in R
R := FreeMagmaRing(Rationals, Mon);
embMonR := x -> ImageElm(Embedding(Mon, R), x); # Embedding Mon -> R
oneR := One(R);
zeroR := Zero(R);
famR := FamilyObj(oneR);
## Generators of Mon
genMon := GeneratorsOfGroup(Mon); # List of generators of Mon, ordered in the same way as ringIndetNames
famMon := FamilyObj(genMon[1]);
xMon := genMon{[1..ring_rank]}; # [ x_1, ..., x_(ring_rank) ]
yMon := genMon{[ring_rank+1..2*ring_rank]}; # [x_1', ..., x_(ring_rank)']
fIndetMon := []; # fIndetMon[i][j] = f(v_i, v_j)
for i in [1..mod_rank] do
	startindex := 2*ring_rank + (i-1)*mod_rank + 1;
	Add(fIndetMon, genMon{[startindex..startindex+mod_rank-1]});
od;
## Generators of R
genR := List(genMon, x -> zeroR + x);
xR := List(xMon, x -> zeroR + x);
yR := List(yMon, x -> zeroR + x);
fIndetR := List(fIndetMon, x -> zeroR + x);
# For involution map
# [f(v_1, v_1),...,f(v_i, v_j),...,f(v_(mod_rank), v_(mod_rank)]
fIndetMonList := Concatenation(fIndetMon); 
# [-f(v_1, v_1),...,-f(v_j, v_i),...,-f(v_(mod_rank), v_(mod_rank)]
fIndetRInvList := [];
for i in [1..mod_rank] do
	for j in [1..mod_rank] do
		Add(fIndetRInvList, -fIndetR[j][i]);
	od;
od;

## Functions which compute indeterminate number in genomMon/genR
# Indeterminate number of x_i in genMon/genR
xIndetNum := function(i)
	return i;
end;

# Indeterminate number of y_i in genMon/genR
yIndetNum := function(i)
	return i + ring_rank;
end;

# Indeterminate number of f(v_i, v_j) in genMon/genR
fIndetNum := function(i, j)
	return 2*ring_rank + (i-1)*mod_rank + j;
end;

# ------ End of R ------

# ---- The modules F_pos and F_neg ------

b := []; # List of basis vectors for F_pos and F_neg
for i in [1..n] do
	b[i] := [];
	for j in [1..n] do
		if j = i then
			Add(b[i], oneR);
		else
			Add(b[i], zeroR);
		fi;
	od;
od;
# Zero vector in F_pos and F_neg
zeroFree := NullMat(1, n, R)[1];

# -----------------------

# ---- The module M --------
v := []; # List of "basis" vectors for M
for i in [1..mod_rank] do
	v[i] := [];
	for j in [1..mod_rank] do
		if j = i then
			Add(v[i], oneR);
		else
			Add(v[i], zeroR);
		fi;
	od;
od;

zeroM := NullMat(1, mod_rank, R)[1]; # Zero vector in M
# ------------

# ---- The module V = M + F_pos + F_neg ------
vEmbed := List(v, x -> [ x, zeroFree, zeroFree ]);
bPos := List(b, x -> [ zeroM, x, zeroFree ]);
bNeg := List(b, x -> [ zeroM, zeroFree, x ]);
# --------------------

# ----- Involution on R -----------------

## To define the involution, we need some auxiliary functions

# r: Element of R.
# monList, ringList: Lists of elements (only generators) of Mon/R of the same length
# Output: The element obtained from r by replacing every occurence of monList[i] by ringList[i] for all i
replaceR := function(r, monList, ringList)
	local coeffList, result, monNumList, i, k, word, magmaEl, coeff, replacement, genNum;
	# E.g. if r = x_1 + 2 * x_2 * y_1, then coeffList = [x_1, 1, x_2 * y_1, 2]
	coeffList := CoefficientsAndMagmaElements(r);
	result := zeroR;
	# List of the numbers of the generators in monList
	monNumList := List(monList, x -> Position(genMon, x));
	# Go through all summands of r
	for i in [1..Length(coeffList)/2] do
		magmaEl := coeffList[2*i - 1];
		coeff := coeffList[2*i];
		# magmaEl will be replaced by this element of R
		replacement := oneR;
		# e.g. if magmaEl = x_2 * y_1, then word = [2, ring_rank+1]
		word := LetterRepAssocWord(magmaEl, genMon);
		for genNum in word do
			if genNum in monNumList then # Replace generator
				k := Position(monNumList, genNum);
				replacement := replacement * ringList[k];
			elif -genNum in monNumList then # For inverses of generators
				k := Position(monNumList, -genNum);
				replacement := replacement * ringList[k]^-1;
			else # No replacement
				if genNum > 0 then
					replacement := replacement * genMon[genNum];
				else
					replacement := replacement * genMon[-genNum]^-1;
				fi;
			fi;
		od;
		# New summand
		result := result + coeff * replacement;
	od;
	return result;
end;

# Additive map R -> R, a_1...a_n -> a_n...a_1 (for a_i \in Mon)
reverseR := function(r)
	local coeffList, result, i, magmaEl, coeff, w;
	coeffList := CoefficientsAndMagmaElements(r);
	result := zeroR;
	for i in [1..Length(coeffList)/2] do
		magmaEl := coeffList[2*i - 1];
		coeff := coeffList[2*i];
		w := LetterRepAssocWord(magmaEl, genMon);
		w := Reversed(w);
		magmaEl := AssocWordByLetterRep(famMon, w, genMon);
		result := result + ElementOfMagmaRing(famR, Zero(coeff), [coeff], [magmaEl]);
	od;
	return result;
end;

# Involution map R -> R
inv := function(r)
	local i, j;
	r := reverseR(r);
	r := replaceR(r, Concatenation(xMon, yMon, fIndetMonList), Concatenation(yR, xR, fIndetRInvList));
	return r;
end;

# ----- End of involution -------------

# ---- Other functions between R and M ---------
# Skew-hermitian form f: M x M -> R
# f(\sum_i v_i a_i, \sum_j w_j b_j) = sum_{i,j} a_i' f(v_i, w_j) b_j
f := function(mpart1, mpart2)
	local sum, i, j;
	sum := zeroR;
	for i in [1..mod_rank] do
		for j in [1..mod_rank] do
			sum := sum + inv(mpart1[i]) * fIndetR[i][j] * mpart2[j];
		od;
	od;
	return sum;
end;

# Trace function Tr: R x R -> R
Tr := function(r, s)
	return r * inv(s) + s * inv(r);
end;

# ----- End of other functions

# ----- Auxiliary functions ----

# Returns -1 if bool is true, 1 otherwise
dminus := function(bool)
	if bool then return -1;
	else return 1; fi;
end;

# dinv(bool) is the involution map if bool is true, identity map otherwise
dinv := function(bool)
	if bool then return (x -> inv(x));
	else return (x -> x); fi;
end;

# Returns the set of numbers "between" i and j, including i and j
bet := function(i, j)
	if i < j then return [i..j];
	else return [j..i]; fi;
end;

# ----- End of Auxiliary ----