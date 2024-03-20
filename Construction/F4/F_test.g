### Fifth file to load.
### In this file, we define various functions which verify that
### the desired commutator relations and conjugation formulas hold.
### Each test function prints an "alarm" string if some computation does not
### match the desired outcome. Otherwise it prints and returns nothing.

# Prints all values of the parity map that are given in 10.4.19 in my PhD thesis.
computeAllNeededParities := function()
	local alpha, deltaList, list, neededList;
	neededList := [ [ f2, [ f1 ] ], [ f2, [ f1, f1 ] ],
		[ f2, [ f1, f2 ]], [ f2, [ f3 ] ],
		[ f3, [ f4 ] ], [ f3, [ f4, f4 ] ],
		[ f3, [ f2 ] ], [ f3, [ f4, f3 ] ],
		[ f3, [ -f2, f3, f2 ]],
		[ f2, [ f1 ] ]
	];
	for list in neededList do
		alpha := list[1];
		deltaList := list[2];
		Print("eta_(", alpha, ", ", deltaList, ") = ", F4ParityForWord(alpha, deltaList), "\n");
	od;
end;

# Tests whether all entries of the parity map are well-defined (i.e. no fail). I.e. verifies 10.4.8 and 10.4.13 in my PhD thesis.
testAllParityValid := function()
	local alpha, delta, numProblems, problemPairs;
	numProblems := 0;
	# problemPairs := [];
	for alpha in F4LinCom do
		# for delta in [ f1, f2, f3, f4 ] do
		for delta in F4LinCom do
			if F4Parity(alpha, delta) = fail then
				numProblems := numProblems + 1;
				# Add(problemPairs, [ alpha, F4refl(delta, alpha) ]);
				Display("Problem for: ");
				Display(alpha);
				Display(delta);
			fi;
		od;
	od;
	# Print("Number of problems: ", numProblems, "\n");
	# return problemPairs;
end;

# Tests whether F4Parity(alpha, delta) = F4Parity(-alpha, delta) for all alpha in F_4 and all simple delta. I.e. verifies the corresponding assertion in 10.4.13 in my PhD thesis.
testParityNeg := function()
	local alpha, delta;
	for alpha in F4LinCom do
		for delta in [ f1, f2, f3, f4 ] do
			if F4Parity(alpha, delta) <> F4Parity(-alpha, delta) then
				Display("Problem");
			fi;
		od;
	od;
end;

# Prints latex table which displays all values F4ParityList(alpha, delta) for positive alpha and simple delta
printPosParityTableTex := function()
	local alpha, a, i;
	for alpha in F4PosSysAsLinCom() do
		# Print alpha
		Print("\$ ");
		for a in alpha do
			Print(a);
		od;
		Print(" \$");
		# Print parity values
		for i in [1..4] do
			Print(" \& \$ (");
			Print(F4Parity(-alpha, f[i])[1]);
			Print(", ");
			Print(F4Parity(-alpha, f[i])[2]);
			Print(") \$");
		od;
		Print(" \\\\");
		Print("\n");
	od;
end;

# Tests whether the second component of the parity map is square-invariant. I.e. verifies part of 10.6.3 in my PhD thesis.
testInvoParSquareTriv := function()
	local alpha, delta, numProblems;
	numProblems := 0;
	for alpha in F4LinCom do
		if not F4RootIsShort(alpha) then
			continue;
		fi;
		for delta in [ f1, f2, f3, f4 ] do
			if F4ParityForWord(alpha, [ delta, delta ])[2] = -1 then
				numProblems := numProblems + 1;
				# Add(problemPairs, [ alpha, F4refl(delta, alpha) ]);
				Display("Problem for: ");
				Display(alpha);
				Display(delta);
			fi;
		od;
	od;
end;

# Tests whether for all orthogonal alpha, delta s.t. delta is simple, the second component of the parity map equals 1 if and only if alpha and delta are crystallographically adjacent. I.e. verifies 10.4.20 in my PhD thesis.
testInvoParStabComp := function()
	local alpha, delta, numProblems;
	numProblems := 0;
	for delta in [ f1, f2, f3, f4 ] do
		for alpha in F4OrthogonalRoots(delta) do
			if alpha + delta in F4LinCom then # alpha, delta are not crystallographically adjacent
				if F4Parity(alpha, delta)[2] = 1 then
					numProblems := numProblems + 1;
					# Add(problemPairs, [ alpha, F4refl(delta, alpha) ]);
					Display("Problem for: ");
					Display(alpha);
					Display(delta);
				fi;
			else # alpha, delta are adjacent
				if F4Parity(alpha, delta)[2] = -1 then
					numProblems := numProblems + 1;
					# Add(problemPairs, [ alpha, F4refl(delta, alpha) ]);
					Display("Problem for: ");
					Display(alpha);
					Display(delta);
				fi;
			fi;
		od;
	od;
end;

# Tests the commutator relations in 10.4.18 in my PhD thesis.
testCommRel := function()
	local x1, x2, x3, x4, comm;
	x1 := Indeterminate(F, 1);
	x2 := Indeterminate(F, 2);
	x3 := Indeterminate(F, 3);
	x4 := Indeterminate(F, 4);
	comm := function(x, y)
		return x^-1 * y^-1 * x * y;
	end;
	# [f_1, f_2]
	if comm(F4Roothom(f1, x1), F4Roothom(f2, x2)) <> F4Roothom(f1+f2, -x1*x2) then
		Display("Problem for f1, f2");
	fi;
	# [f_2, f_3]
	if comm(F4Roothom(f2, x1), F4Roothom(f3, x2, x3)) <> F4Roothom(f2+f3, -x1*x2, -x1*x3) * F4Roothom(f2+2*f3, -x1*x2*x3) then
		Display("Problem for f2, f3");
	fi;
	# [f_2 + f_3, f_3 ]
	if comm(F4Roothom(f2+f3, x1, x2), F4Roothom(f3, x3, x4)) <> F4Roothom(f2+2*f3, x1*x4 + x3*x2) then
		Display("Problem for f2+f3, f3");
	fi;
	# [f_4, f_3]
	if comm(F4Roothom(f4, x1, x2), F4Roothom(f3, x3, x4)) <> F4Roothom(f3+f4, x1*x3, x2*x4) then
		Display("Problem for f4, f3");
	fi;
end;

testAll := function()
	testAllParityValid();
	testCommRel();
	testInvoParSquareTriv();
	testInvoParStabComp();
	testParityNeg();
end;