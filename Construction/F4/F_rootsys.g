### First file to load.
### In this file, we define functions for dealing with the root systems F_4 and E_6.
### Everything here is purely combinatorial: There are no groups here.

## We will use 3 different formats to represent roots in a root system Roots with basis Basis:
# 1. As a linear combination of simple roots, i.e. by a list l which represents \sum_i l[i]*Basis[i]. This is the format which I prefer to work with. ("Linear combination format")
# 2. As the list of their Cartan integers with the simple roots. ("Cartan format") This is format which GAP uses to represent roots, and this is the only reason why we use it. We will have no need to use it for F_4.
# 3. By a number between 1 and |Roots|. This is the format that GAP uses for the generators of the corresponding simple Lie algebra. ("Numbering format")

## Standard ordering of the roots in F_4: (as in Humphreys, Lie algebras, page 58)
# 1-2>3-4
## Standard ordering of the roots in E_6:
#     2
#     |
# 1-3-4-5-6

# ----- E_6 in the Cartan format, setup ----

F := Rationals; # The ground field
E6Lie := SimpleLieAlgebra("E", 6, F);
E6Car := RootSystem(E6Lie); # Root system in the Cartan format
E6CarPos := PositiveRoots(E6Car); # List of positive roots in E_6 in the Cartan format
E6CarSim := SimpleSystem(E6Car); # List of simple roots in E_6 in the Cartan format

# ------ End of E_6 in Cartan format ----

# ----- Linear combination format, setup -------

# Simple roots in E_6
e := [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]];
e1 := e[1];
e2 := e[2];
e3 := e[3];
e4 := e[4];
e5 := e[5];
e6 := e[6];

# Simple roots in F_4
f := [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]];
f1 := f[1];
f2 := f[2];
f3 := f[3];
f4 := f[4];

# Returns a list of all positive roots in E_6 in the linear combination format
E6PosSysAsLinCom := function()
	local result, counter, interval, a, b, c, d, e, f, root;
	result := [];
	counter := 0;
	interval := [0..4];
	for a in interval do
		for b in interval do
			for c in interval do
				for d in interval do
					for e in interval do
						for f in interval do
							root := [ a, b, c, d, e, f ];
							if root*E6CarSim in E6CarPos then
								Add(result, root);
								counter := counter+1;
								if counter = 36 then # Known number of positive roots in E_6
									return result;
								fi;
							fi;
						od;
					od;
				od;
			od;
		od;
	od;
	return result;
end;

# Returns a list of all positive roots in F_4 in the linear combination format
F4PosSysAsLinCom := function()
	local f1, f2, f3, f4;
	f1 := f[1];
	f2 := f[2];
	f3 := f[3];
	f4 := f[4];
	return [ f1, f2, f3, f4, f1+f2, f2+f3, f3+f4, f1+f2+f3, f2+2*f3, f2+f3+f4, f1+f2+2*f3, f1+f2+f3+f4, f2+2*f3+f4, f1+2*f2+2*f3, f1+f2+2*f3+f4, f2+2*f3+2*f4, f1+2*f2+2*f3+f4, f1+f2+2*f3+2*f4, f1+2*f2+3*f3+f4, f1+2*(f2+f3+f4), f1+2*f2+3*f3+2*f4, f1+2*f2+4*f3+2*f4, f1+3*f2+4*f3+2*f4, 2*f1+3*f2+4*f3+2*f4 ]; # Positive Roots in the order given by Vavilov-Plotkin
end;

# The whole root systems. The ordering of F4LinCom is precisely the one defined in 10.4.4 of my PhD thesis.
E6LinCom := Concatenation(E6PosSysAsLinCom(), -E6PosSysAsLinCom());
F4LinCom := Concatenation(F4PosSysAsLinCom(), -F4PosSysAsLinCom());

# ----- End of linear combination format, setup -----

# ----- Conversion functions for the different formats of roots ----

# root: A root of E_6, given as a linear combination of simple roots
# Output: The same root in the Cartan format
E6LinComToCartan := function(root)
	return root * E6CarSim;
end;

# root: A root of E_6, given in the Cartan format
# Output: The same root in the numbering format (i.e. the number of this root)
E6CartanToNumber := function(root)
	local k;
	k := Position(E6CarPos, root);
	if k <> fail then
		return k;
	fi;
	k := Position(E6CarPos, -root);
	if k <> fail then
		return Length(E6CarPos) + k;
	fi;
	return fail;
end;

E6LinComToNumber := root -> E6CartanToNumber(E6LinComToCartan(root)); # Runtime is irrelevant

F4LinComToNumber := function(root)
	return Position(F4LinCom, root);
end;

F4NumberToLinCom := function(rootnumber)
	return F4LinCom[rootnumber];
end;

# ----- End of conversion functions -----

# ----- Functions for inner product and reflections in F_4 ---

# alpha, beta: Roots in F_4, given as linear combinations of simple roots
# Output: Their inner product
F4InnerProduct := function(alpha, beta)
	local mat;
	# mat[i][j] is the inner product of f[i] with f[j]
	mat := [[ 2, -1, 0, 0], [ -1, 2, -1, 0 ], [ 0, -1, 1, -1/2 ], [ 0, 0, -1/2, 1 ] ];
	return alpha * mat * beta;
end;

# alpha, beta: Roots in F_4 in the linear combination format
# Output: sigma_alpha(beta) in the linear combination format
F4refl := function(alpha, beta)
	return beta - (2 * F4InnerProduct(alpha, beta) / F4InnerProduct(alpha, alpha))*alpha;
end;

# alpha: Root in F_4 in the linear combination format
# Output: Set of all roots in F_4 which are orthogonal to alpha (in the linear combination format)
F4OrthogonalRoots := function(alpha)
	local result, beta;
	result := [];
	for beta in F4PosSysAsLinCom() do
		if F4InnerProduct(alpha, beta) = 0 then
			Add(result, beta);
			Add(result, -beta);
		fi;
	od;
	return result;
end;

# root: Root in F_4 in the linear combination format
# Output: true if root is short, otherwise false
F4RootIsShort := function(root)
	if F4InnerProduct(root, root) = 1 then
		return true;
	else
		return false;
	fi;
end;

# ---- End of F_4 functions ----

# ---- The folding E_6 -> F_4 ---

# alpha: Root in F_4 in the linear combination format
# Output: The preimage of alpha in E_6 under the projection map in the folding. This is always a list of length 2: If the preimage consists of only 1 element, then this element appears twice in the list. The ordering of the roots in this list is always the one which is induced by the ordering of E6LinCom, i.e. the one in 10.4.4 of my PhD thesis.
## We will fold as follows:
#            3-1
#           /
# E_6 =  2-4
#           \
#            5-6
# becomes
# F_4 =  1-2>3-4
# I.e. 2 -> 1, 4 -> 2, { 3, 5 } -> 3, { 1, 6 } -> 4
F4ToE6OnLinCom := function(alpha)
	## Explanation:
	# Consider the 6-dimensional vector space in which E_6 lives. We have an involution inv of this space defined by e_1 <-> e_6 and e_3 <-> e_5 and by fixing e_2 and e_4, where e_1, ..., e_6 is the root base of E_6 in standard ordering. The fixed space Fix of inv is 4-dimensional and the orthogonal projection pi of E_6 to Fix is F_4. Fix is spanned by e_2, e_4, e_1 + e_6, e_3 + e_5 and its orthogonal complement Orth is spanned by e_1 - e_6, e_3 - e_5.
	# For each root alpha of E_6, there are two possibilities:
	# 1. alpha is fixed by inv and alpha is the only root of E_6 which is mapped to alpha by pi.
	# 2. alpha is not fixed by inv and there is exactly one other root beta of E_6 with pi(alpha) = pi(beta).
	# Thus each root alpha in F_4 can be represented by a pair of roots phi(alpha) = (beta, gamma) in E_6 such that alpha = pi(beta) = pi(gamma) and we have beta = gamma if and only if alpha is in case 1. In fact, we have alpha = (beta+gamma)/2. This GAP function computes phi. For the simple roots f_1, ..., f_4 in F_4, we already know phi(f_1), ..., phi(f_4) (see folding diagram). If alpha = \sum a_i f_i is any root in F_4, then beta = \sum a_i phi(f_i) is a pair of roots in E_6 which project to alpha under pi, so the roots in phi(alpha) lie in beta + Orth. Thus to compute phi(alpha), we only have to find the roots in E_6 which lie in beta + Orth.
	local im1, im2, im3, im4, basisImages, beta, Orth, preimageRoots, gamma;
	# Images of the four simple roots in F_4
	im1 := [[0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0]]; # phi(f_1)
	im2 := [ [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0] ]; # phi(f_2)
	im3 := [ [0, 0, 1, 0, 0, 0], [ 0, 0, 0, 0, 1, 0 ] ]; # phi(f_3)
	im4 := [ [1, 0, 0, 0, 0, 0], [ 0, 0, 0, 0, 0, 1 ] ]; # phi(f_4)
	basisImages := [ im1, im2, im3, im4 ];
	beta := alpha * basisImages; # beta = \sum a_i phi(f_i)
	Orth := VectorSpace(Rationals, [ e[1] - e[6], e[3] - e[5] ]);
	preimageRoots := [];
	for gamma in E6LinCom do
		# Since beta[1] + Orth = beta[2] + Orth, we do not have to check for beta[2]. Thus we could actually remove the second entries from im1, ..., im2.
		if gamma - beta[1] in Orth then
			Add(preimageRoots, gamma);
		fi;
	od;
	if Length(preimageRoots) = 1 then
		return [ preimageRoots[1], preimageRoots[1] ];
	else
		return preimageRoots;
	fi;
end;

# ----- End of folding ----