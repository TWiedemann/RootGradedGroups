### Fourth file to load.
### In this file we define functions to compute and use the parity maps.

# alpha, delta: Roots in F_4 in the linear combination format
# Output: A tuple (a, b) s.t. x_alpha^{w_delta}(r, s) = x_{refl(alpha, delta)}( (a,b).(r, s) ) for r, s \in F
# where (-1, 1).(r, s) = (-r, s) (inversion action) and (1, -1).(r, s) = (s, r) (switching involution).
computeF4Parity := function(alpha, delta)
	local w, x1, x2, gamma, conj;
	w := F4WeylStandard(delta);
	x1 := Indeterminate(F, 1);
	x2 := Indeterminate(F, 2);
	gamma := F4refl(delta, alpha);
	if F4RootIsShort(alpha) then
		conj := w^-1 * F4Roothom(alpha, x1, x2) * w;
		if conj = F4Roothom(gamma, -x1, -x2) then
			return [ -1, 1 ];
		elif conj = F4Roothom(gamma, x2, x1) then
			return [ 1, -1 ];
		elif conj = F4Roothom(gamma, x1, x2) then
			return [ 1, 1 ];
		elif conj = F4Roothom(gamma, -x2, -x1) then
			return [ -1, -1];
		else
			return fail;
		fi;
	else
		conj := w^-1 * F4Roothom(alpha, x1) * w;
		if conj = F4Roothom(gamma, x1) then
			return [ 1, 1 ];
		elif conj = F4Roothom(gamma, -x1) then
			return [ -1, 1 ];
		else
			return fail;
		fi;
	fi;
end;

# Output: A table tab s.t. tab[i][j] = computeF4Parity(alpha_i, alpha_j) where alpha_i, alpha_j are the roots in F_4 with numbers i and j
computeF4ParityList := function()
	local result, i, j;
	result := [];
	for i in [1..Length(F4LinCom)] do
		result[i] := [];
		for j in [1..Length(F4LinCom)] do
			result[i][j] := computeF4Parity(F4NumberToLinCom(i), F4NumberToLinCom(j));
		od;
	od;
	return result;
end;

# Computes the parity table for F_4 and writes it to a file on the Desktop. This works on Windows, I don't know about your operating system. Better comment it out for safety.
# writeF4ParityListToFile := function()
	# local outputFile, F4ParityList;
	# outputFile := OutputTextFile("Desktop/F_paritylist.g", false);
	# SetPrintFormattingStatus(outputFile, false);
	# PrintTo(outputFile); # Make file empty
	# F4ParityList := computeF4ParityList();
	# AppendTo(outputFile, "F4ParityList := ");
	# AppendTo(outputFile, F4ParityList);
	# AppendTo(outputFile, ";");
	# return F4ParityList;
# end;

# alpha, delta: Roots in F_4 in the linear combination format
# Output: The parity map at position (alpha, delta).
# For a better runtime, the parity map was pre-computed and stored in F_paritylist.g.
F4Parity := function(alpha, delta)
	return F4ParityList[F4LinComToNumber(alpha)][F4LinComToNumber(delta)];
end;

F4ParityForWord := function(alpha, deltaList)
	local result, delta, parity;
	result := [ 1, 1];
	for delta in deltaList do
		parity := F4Parity(alpha, delta);
		alpha := F4refl(delta, alpha);
		result := [ result[1] * parity[1], result[2] * parity[2] ];
	od;
	return result;
end;