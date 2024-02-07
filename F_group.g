### Second file to load.
### In this file, we define an F_4-graded group by folding a Chevalley group of type E_6.
### The Chevalley group is defined over the ground field F. The short root groups of the
### F_4-graded group are parametrised by F x F and the long root groups by F.

# ---- Construction of the Chevalley group ---

# The Chevalley group is defined with respect to some module V over E6Lie.
# The particular choice of V is irrelevant, but we chooose it so that its
# dimension is minimal.
V := HighestWeightModule(E6Lie, [1, 0, 0, 0, 0, 0]);
VBas := Basis(V);
dimV := Dimension(V);

# x: Element of E6Lie
# Returns the matrix of x with respect to VBas (as a left action on column vectors)
repMatrix := function(x)
	local result, i;
	result := [];
	for i in [1..dimV] do
		Add(result, Coefficients(VBas, x^VBas[i]));
	od;
	return TransposedMat(result);
end;

# Returns id + mat + mat^2/2 + mat^3/3! + ...
matrixExp := function(mat)
	local result, A, n;
	result := mat^0;
	A := mat;
	n := 1;
	while not IsZero(A) do
		result := result + A;
		n := n+1;
		A := A*mat/n;
	od;
	return result;
end;

# root: A root of E6 in the numbering format
# r: An element of F.
# Output: x_root(r) where x_root is the root homomorphism in the Chevalley group
E6RoothomOnNumber := function(root, r)
	return matrixExp(r*repMatrix(E6Lie.(root)));
end;

# ----- End of Chevalley group ----

# ----- Construction of the F_4-graded group ----

# F4Roothom takes two arguments (a root and an element of F) if the root is long and three arguments (a root and two elements of F) if the root is short. Hence we declare it as an operation.
DeclareOperation("F4Roothom", [ IsList, IsObject ]);
DeclareOperation("F4Roothom", [ IsList, IsObject, IsObject ]);

# List of positive short roots for which the root homomorphism is twisted by a sign (10.4.10 in PhD thesis). All corresponding negative root homomorphisms are twisted as well.
F4TwistRoots := [ f2+f3, -f2-f3, f3+f4, -f3-f4, f1+f2+f3, -f1-f2-f3, f2+2*f3+f4, -f2-2*f3-f4, f1+f2+2*f3+f4, -f1-f2-2*f3-f4, f1+2*f2+2*f3+f4, -f1-2*f2-2*f3-f4, f1+2*f2+3*f3+2*f4, -f1-2*f2-3*f3-2*f4 ];

# Root homomorphism for short roots
InstallMethod(F4Roothom, [ IsList, IsObject, IsObject ], function(root, r, s)
	local E6RootPair, E6Root1, E6Root2, sign;
	E6RootPair := F4ToE6OnLinCom(root); # The preimage of root in E_6
	if E6RootPair[1] = E6RootPair[2] then # This happens if root is long
		return fail;
	fi;
	E6Root1 := E6LinComToNumber(E6RootPair[1]);
	E6Root2 := E6LinComToNumber(E6RootPair[2]);
	if root in F4TwistRoots then # Twist the second root, as in 10.4.10 of my PhD thesis.
		sign := -1;
	else
		sign := 1;
	fi;
	return E6RoothomOnNumber(E6Root1, r) * E6RoothomOnNumber(E6Root2, sign*s);
end );

# Root homomorphism for long roots
InstallMethod(F4Roothom, [ IsList, IsObject ], function(root, r)
	local E6RootPair, E6Root;
	E6RootPair := F4ToE6OnLinCom(root);
	if E6RootPair[1] <> E6RootPair[2] then # This happens if root is short
		return fail;
	fi;
	E6Root := E6LinComToNumber(E6RootPair[1]);
	return E6RoothomOnNumber(E6Root, r);
end );

# root: A root in F_4 in linear combination format
# Output: The corresponding standard Weyl element
F4WeylStandard := function(root)
	if F4RootIsShort(root) then
		return F4Roothom(-root, -One(F), -One(F)) * F4Roothom(root, One(F), One(F)) * F4Roothom(-root, -One(F), -One(F));
		# F4Weyl(root, One(F), One(F));
	else
		return F4Roothom(-root, -One(F)) * F4Roothom(root, One(F)) * F4Roothom(-root, -One(F));
		# F4Weyl(root, One(F));
	fi;
end;

# ----- End of F_4-graded group construction ----
