### Third file to load.
### In this file, we define various functions which verify that
### the desired commutator relations and conjugation formulas hold.
### Each test function prints an "alarm" string if some computation does not
### match the desired outcome. Otherwise it prints and returns nothing.

# Equality of functions (on V) is tested by evaluating them on VTestGenList.
# Recall that vEmbed[rank-1] exists only for testing purposes and must not be
# used anywhere else.
VTestGenList := Concatenation(bPos, bNeg, [ vEmbed[rank-1] ]);

# Returns true if the two maps func1, func2: V -> V are identical, otherwise false.
funcsAreEqual := function(func1, func2)
	local i, vector;
	for vector in VTestGenList do
		if func1(vector) <> func2(vector) then
			return false;
		fi;
	od;
	return true;
end;

# Tests whether the automorphism auto of V preserves the quadratic form qExt on V
testAutoPreservesQ := function(auto)
	local i, vector1, vector2;
	for vector1 in VTestGenList do
		if qExt(vector1) <> qExt(auto(vector1)) then
			Print("Problem\n");
			return false;
		fi;
	od;
	for vector1 in VTestGenList do
		for vector2 in VTestGenList do
			if fExt(vector1, vector2) <> fExt(auto(vector1), auto(vector2)) then
				Print("Problem\n");
				return false;
			fi;
		od;
	od;
	return true;
end;

# Tests whether all root groups lie in O(qExt)
testRootHomsPreserveQ := function()
	local a, u, i, j;
	a := X(Integers, "a"); # Indeterminate in R
	u := v[1]; # "Indeterminate" in M
	for i in [1..n] do
		for j in [1..n] do
			if i <> j then
				if not testAutoPreservesQ(Xpp(i, j, a)) then
					Print("Problem for +", i, ", +", j, "\n");
				elif not testAutoPreservesQ(Xpm(i, j, a)) then
					Print("Problem for +", i, ", -", j, "\n");
				elif not testAutoPreservesQ(Xmm(i, j, a)) then
					Print("Problem for -", i, ", -", j, "\n");
				fi;
			fi;
		od;
	od;
	for i in [1..n] do
		if not testAutoPreservesQ(Xp(i, u)) then
			Print("Problem for +", i, "\n");
		elif not testAutoPreservesQ(Xm(i, u)) then
			Print("Problem for -", i, "\n");
		fi;
	od;
end;

# Tests commutator relations on pairs of long roots
testLongLongComm := function()
	local a, b, i, j, k, l, x1, x2, y1, y2, comm, result, bool;
	a := X(Integers, "a");
	b := X(Integers, "b");
	for i in [1..n] do
		for j in [1..n] do
			if i = j then
				continue;
			fi;
			for k in [1..n] do
				for l in [1..n] do
					if k = l then
						continue;
					fi;
					# [ e_i - e_j, e_k - e_l ]
					x1 := Xpm(i, j, a);
					x2 := Xpm(i, j, -a);
					y1 := Xpm(k, l, b);
					y2 := Xpm(k, l, -b);
					comm := compose([x2, y2, x1, y1]);
					if j = k and l <> i then
						result := Xpm(i, l, a * b);
					elif i = l and k <> j then
						result := Xpm(k, j, (-1) * a * b);
					else
						result := idMap;
					fi;
					if not(i = l and j = k) then # do not test opposite roots
						if funcsAreEqual(comm, result) = false then
							Print("Problem for +", i, "-", j, ", +", k, "-", l, "\n");
						fi;
					fi;
					
					# [ e_i - e_j, e_k + e_l ]
					x1 := Xpm(i, j, a);
					x2 := Xpm(i, j, -a);
					y1 := Xpp(k, l, b);
					y2 := Xpp(k, l, -b);
					comm := compose([x2, y2, x1, y1]);
					if j = k and l <> i then
						# bool = "l lies between i and j"
						bool := (i < l and l < j) or (j < l and l < i);
						result := Xpp(i, l, dminus(bool) * a * b);
					elif j = l and k <> i then
						# bool = "k lies between i and j"
						bool := (i < k and k < j) or (j < k and k < i);
						result := Xpp(i, k, dminus(bool) * a * b);
					else
						result := idMap;
					fi;
					if funcsAreEqual(comm, result) = false then
						Print("Problem for +", i, "-", j, ", +", k, "+", l, "\n");
					fi;
					
					# [ e_i - e_j, -e_k - e_l ]
					x1 := Xpm(i, j, a);
					x2 := Xpm(i, j, -a);
					y1 := Xmm(k, l, b);
					y2 := Xmm(k, l, -b);
					comm := compose([x2, y2, x1, y1]);
					if i = k and l <> j then
						# bool = "l does not lie between i and j"
						bool := not((i < l and l < j) or (j < l and l < i));
						result := Xmm(j, l, dminus(bool) * a * b);
					elif i = l and k <> j then
						# bool = "k does not lie between i and j"
						bool := not((i < k and k < j) or (j < k and k < i));
						result := Xmm(j, k, dminus(bool) * a * b);
					else
						result := idMap;
					fi;
					if funcsAreEqual(comm, result) = false then
						Print("Problem for +", i, "-", j, ", -", k, "-", l, "\n");
					fi;
					
					# [ e_i + e_j, e_k + e_l ]
					x1 := Xpp(i, j, a);
					x2 := Xpp(i, j, -a);
					y1 := Xpp(k, l, b);
					y2 := Xpp(k, l, -b);
					comm := compose([x2, y2, x1, y1]);
					result := idMap;
					if funcsAreEqual(comm, result) = false then
						Print("Problem for +", i, "+", j, ", +", k, "+", l, "\n");
					fi;
					
					# [ -e_i - e_j, -e_k - e_l ]
					x1 := Xmm(i, j, a);
					x2 := Xmm(i, j, -a);
					y1 := Xmm(k, l, b);
					y2 := Xmm(k, l, -b);
					comm := compose([x2, y2, x1, y1]);
					result := idMap;
					if not IsEqualSet([i, j], [k, l]) then # do not test opposite roots
						if funcsAreEqual(comm, result) = false then
							Print("Problem for -", i, "-", j, ", -", k, "-", l, "\n");
						fi;
					fi;
				od;
			od;
		od;
	od;
end;

# Tests whether root homomorphisms are indeed homomorphisms of groups
testRootHomIsHom := function()
	local u1, u2, a, b, i, j, roothom, prod;
	u1 := v[1];
	u2 := v[2];
	a := X(Integers, "a");
	b := X(Integers, "b");
	# Long roots
	for i in [1..n] do
		for j in [1..n] do
			if i <> j then
				for roothom in [ Xpm, Xpp, Xmm ] do
					prod := compose([ roothom(i, j, a), roothom(i, j, b)]);
					if not funcsAreEqual(prod, roothom(i, j, a+b)) then
						Print("Problem\n");
					fi;
				od;
			fi;
		od;
	od;
	# Short roots
	for i in [1..n] do
		for roothom in [ Xp, Xm ] do
			prod := compose([ roothom(i, u1), roothom(i, u2)]);
			if not funcsAreEqual(prod, roothom(i, u1+u2)) then
				Print("Problem\n");
			fi;
		od;
	od;
end;

# ----- Tests of the commutator relations -----

# Tests commutator relations on pairs (alpha, beta) with alpha long and beta short
testLongShortComm := function()
	local u, a, i, j, k, x1, x2, y1, y2, comm, 
			commpart1, commpart2, result;
	u := v[1];
	a := X(Integers, "a");
	for i in [1..n] do
		for j in [1..n] do
			if i <> j then
				for k in [1..n] do
					# [ e_i - e_j, e_k ]
					x1 := Xpm(i, j, a);
					x2 := Xpm(i, j, -a);
					y1 := Xp(k, u);
					y2 := Xp(k, -u);
					comm := compose([x2, y2, x1, y1]);
					if k = j then
						commpart1 := Xp(i, a*u);
						commpart2 := Xpp(i, j, dminus(i<j) * a * q(u));
						result := compose([commpart1, commpart2]);
					else
						result := idMap;
					fi;
					if funcsAreEqual(comm, result) = false then
						Print("Problem for +", i, "-", j, ", +", k, "\n");
					fi;
					
					# [ e_i - e_j, -e_k ]
					x1 := Xpm(i, j, a);
					x2 := Xpm(i, j, -a);
					y1 := Xm(k, u);
					y2 := Xm(k, -u);
					comm := compose([x2, y2, x1, y1]);
					if i = k then
						commpart1 := Xm(j, -a * u);
						commpart2 := Xmm(i, j, dminus(i>j) * a * q(u));
						result := compose([commpart1, commpart2]);
					else 
						result := idMap;
					fi;
					if funcsAreEqual(comm, result) = false then
						Print("Problem for +", i, "-", j, ", -", k, "\n");
					fi;
					
					# [ e_i + e_j, e_k ]
					x1 := Xpp(i, j, a);
					x2 := Xpp(i, j, -a);
					y1 := Xp(k, u);
					y2 := Xp(k, -u);
					comm := compose([x2, y2, x1, y1]);
					result := idMap;
					if funcsAreEqual(comm, result) = false then
						Print("Problem for +", i, "+", j, ", +", k, "\n");
					fi;
					
					# [ e_i + e_j, -e_k ]
					x1 := Xpp(i, j, a);
					x2 := Xpp(i, j, -a);
					y1 := Xm(k, u);
					y2 := Xm(k, -u);
					comm := compose([x2, y2, x1, y1]);
					if k = i then
						commpart1 := Xp(j, dminus(j<i) * a * u);
						commpart2 := Xpm(j, i, dminus(j<i) * a * q(u));
						result := compose([commpart1, commpart2]);
					elif k = j then
						commpart1 := Xp(i, dminus(i<j) * a * u);
						commpart2 := Xpm(i, j, dminus(i<j) * a * q(u));
						result := compose([commpart1, commpart2]);
					else 
						result := idMap;
					fi;
					if funcsAreEqual(comm, result) = false then
						Print("Problem for +", i, "+", j, ", -", k, "\n");
					fi;
					
					# [ -e_i - e_j, e_k ]
					x1 := Xmm(i, j, a);
					x2 := Xmm(i, j, -a);
					y1 := Xp(k, u);
					y2 := Xp(k, -u);
					comm := compose([x2, y2, x1, y1]);
					if k = i then
						commpart1 := Xm(j, dminus(j>i) * a * u);
						commpart2 := Xpm(i, j, dminus(j<i) * a * q(u));
						result := compose([commpart1, commpart2]);
					elif k = j then
						commpart1 := Xm(i, dminus(i>j) * a * u);
						commpart2 := Xpm(j, i, dminus(i<j) * a * q(u));
						result := compose([commpart1, commpart2]);
					else 
						result := idMap;
					fi;
					if funcsAreEqual(comm, result) = false then
						Print("Problem for -", i, "-", j, ", +", k, "\n");
					fi;
					
					# [ -e_i - e_j, -e_k ]
					x1 := Xmm(i, j, a);
					x2 := Xmm(i, j, -a);
					y1 := Xm(k, u);
					y2 := Xm(k, -u);
					comm := compose([x2, y2, x1, y1]);
					result := idMap;
					if funcsAreEqual(comm, result) = false then
						Print("Problem for -", i, "-", j, ", -", k, "\n");
					fi;
				od;	
			fi;
		od;
	od;
end;

# Tests commutator relations on pairs of short roots
testShortShortComm := function()
	local u1, u2, x1, x2, y1, y2, z, i, j;
	u1 := v[1];
	u2 := v[2];
	# ++
	for i in [1..n] do
		for j in [1..n] do
			x1 := Xp(i, u1);
			x2 := Xp(i, -u1);
			y1 := Xp(j, u2);
			y2 := Xp(j, -u2);
			if i <> j then
				z := Xpp(i, j, dminus(i<j) * f(u1, u2));
			else
				z := idMap;
			fi;
			if funcsAreEqual(z, compose([x2, y2, x1, y1])) = false then
				Print("Problem for +", i, ", +", j, "\n");
			fi;
		od;
	od;
	# +-
	for i in [1..n] do
		for j in [1..n] do
			if i <> j then
				x1 := Xp(i, u1);
				x2 := Xp(i, -u1);
				y1 := Xm(j, u2);
				y2 := Xm(j, -u2);
				z := Xpm(i, j, f(u1, u2));
				if funcsAreEqual(z, compose([x2, y2, x1, y1])) = false then
					Print("Problem for +", i, ", -", j, "\n");
				fi;
			fi;
		od;
	od;
	# --
	for i in [1..n] do
		for j in [1..n] do
			x1 := Xm(i, u1);
			x2 := Xm(i, -u1);
			y1 := Xm(j, u2);
			y2 := Xm(j, -u2);
			if i <> j then
				z := Xmm(i, j, dminus(i>j) * f(u1, u2));
			else
				z := idMap;
			fi;
			if funcsAreEqual(z, compose([x2, y2, x1, y1])) = false then
				Print("Problem for -", i, ", -", j, "\n");
			fi;
		od;
	od;
	return;
end;

# Tests all commutator relations
testAllComm := function()
	testLongLongComm();
	testLongShortComm();
	testShortShortComm();
end;

# ----- End of commutator relations -------

# ----- Test of conjugation formulas for Weyl elements ------

# Tests short Weyl elements on long root groups
testShortWeylOnLong := function()
	local a, u, i, j, k, w, wInv, x, y;
	a := X(Integers, "a");
	u := v[1];
	for i in [1..n] do
		w := Wp(i, u);
		wInv := Wp(i, -u);
		for j in [1..n] do
			for k in [1..n] do
				if j = k then
					continue;
				fi;
				# e_j - e_k
				x := Xpm(j, k, a);
				if i = j then
					y := Xmm(j, k, dminus(i>k)*q(u)^-1 * a);
				elif i = k then
					y := Xpp(j, k, dminus(i>j)*q(u)*a);
				else
					y := x;
				fi;
				if funcsAreEqual(compose([wInv, x, w]), y) = false then
					Print("Problem for ", j, "-", k, ", ", i, "\n");
				fi;
				# e_j + e_k
				x := Xpp(j, k, a);
				if i = j then
					y := Xpm(k, j, dminus(i>k)*q(u)^-1*a);
				elif i = k then
					y := Xpm(j, k, dminus(i>j)*q(u)^-1*a);
				else
					y := x;
				fi;
				if funcsAreEqual(compose([wInv, x, w]), y) = false then
					Print("Problem for ", j, "+", k, ", ", i, "\n");
				fi;
				# -e_j - e_k
				x := Xmm(j, k, a);
				if i = j then
					y := Xpm(j, k, dminus(i>k)*q(u)*a);
				elif i = k then
					y := Xpm(k, j, dminus(i>j)*q(u)*a);
				else
					y := x;
				fi;
				if funcsAreEqual(compose([wInv, x, w]), y) = false then
					Print("Problem for -", j, "-", k, ", ", i, "\n");
				fi;
			od;
		od;
	od;
end;

# Tests short Weyl elements on short root groups
testShortWeylOnShort := function()
	local u1, u2, i, j, w, wInv, x, y;
	u1 := v[1];
	u2 := v[2];
	for i in [1..n] do
		w := Wp(i, u1);
		wInv := Wp(i, -u1);
		for j in [1..n] do
			# +e_j
			x := Xp(j, u2);
			if i = j then
				y := Xm(j, q(u1)^-1 * refl(u1, u2));
			else
				y := Xp(j, refl(u1, u2));
			fi;
			if funcsAreEqual(compose([wInv, x, w]), y) = false then
				Print("Problem for ", j, ", ", i, "\n");
			fi;
			# -e_j
			x := Xm(j, u2);
			if i = j then
				y := Xp(j, q(u1) * refl(u1, u2));
			else
				y := Xm(j, refl(u1, u2));
			fi;
			if funcsAreEqual(compose([wInv, x, w]), y) = false then
				Print("Problem for -", j, ", ", i, "\n");
			fi;
		od;
	od;
end;

# Tests long Weyl elements on long root groups
testLongWeylOnLong := function()
	local a, b, i, j, k, l, p, x, y, w, wInv;
	a := X(Integers, "a");
	b := X(Integers, "b");
	for i in [1..n] do
		for j in [1..n] do
			if i = j then
				continue;
			fi;
			w := Wpm(i, j, a);
			wInv := Wpm(i, j, -a);
			for k in [1..n] do
				for l in [1..n] do
					if k = l then
						continue;
					fi;
					# e_k - e_l
					x := Xpm(k, l, b);
					if i = k then
						if l = j then
							y := Xpm(j, i, -a^-1 * b * a^-1);
						else
							y := Xpm(j, l, a^-1*b);
						fi;
					elif i = l then
						if k = j then
							y := Xpm(i, j, -a*b*a);
						else
							y := Xpm(k, j, b*a);
						fi;
					else
						if j = k then
							y := Xpm(i, l, -a*b);
						elif j = l then
							y := Xpm(k, i, -b*a^-1);
						else
							y := x;
						fi;
					fi;
					if funcsAreEqual(compose([wInv, x,w]), y) = false then
						Print("Problem for ", i, "-", j, " on ", k, "-", l, "\n");
					fi;
					# e_k + e_l
					x := Xpp(k, l, b);
					if i in [k, l] then
						# Define p so that { k, l } = { i, p }
						if i = k then
							p := l;
						else
							p := k;
						fi;
						if p = j then
							y := Xpp(i, j, b);
						else
							y := Xpp(j, p, dminus(between(p, i, j))*a^-1*b);
						fi;
					elif j in [k, l] then
						# Define p so that { k, l } = { j, p }
						if j = k then
							p := l;
						else
							p := k;
						fi;
						# We automatically have i <> p because not i in [k, l]
						y := Xpp(i, p, -dminus(between(p, i, j))*a*b);
					else
						y := x;
					fi;
					if funcsAreEqual(compose([wInv, x,w]), y) = false then
						Print("Problem for ", i, "-", j, " on ", k, "+", l, "\n");
					fi;
					# -e_k - e_l
					x := Xmm(k, l, b);
					if i in [k, l] then
						# Define p so that { k, l } = { i, p }
						if i = k then
							p := l;
						else
							p := k;
						fi;
						if p = j then
							y := Xmm(i, j, b);
						else
							y := Xmm(j, p, dminus(between(p, i, j))*a*b);
						fi;
					elif j in [k, l] then
						# Define p so that { k, l } = { j, p }
						if j = k then
							p := l;
						else
							p := k;
						fi;
						# We automatically have i <> p because not i in [k, l]
						y := Xmm(i, p, -dminus(between(p, i, j))*a^-1*b);
					else
						y := x;
					fi;
					if funcsAreEqual(compose([wInv, x,w]), y) = false then
						Print("Problem for ", i, "-", j, " on -", k, "-", l, "\n");
					fi;
				od;
			od;
		od;
	od;
end;

# Tests longs Weyl elements on short root groups
testLongWeylOnShort := function()
	local i, j, k, u, a, w, wInv, x, y;
	u := v[1];
	a := X(Integers, "a");
	for i in [1..n] do
		for j in [1..n] do
			if i = j then
				continue;
			fi;
			w := Wpm(i, j, a);
			wInv := Wpm(i, j, -a);
			for k in [1..n] do
				# e_k
				x := Xp(k, u);
				if i = k then
					y := Xp(j, a^-1*u);
				elif j = k then
					y := Xp(i, -a*u);
				else
					y := x;
				fi;
				if funcsAreEqual(compose([wInv, x, w]), y) = false then
					Print("Problem for ", i, "-", j, " on +", k, "\n");
				fi;
				# -e_k
				x := Xm(k, u);
				if i = k then
					y := Xm(j, a*u);
				elif j = k then
					y := Xm(i, -a^-1*u);
				else
					y := x;
				fi;
				if funcsAreEqual(compose([wInv, x, w]), y) = false then
					Print("Problem for ", i, "-", j, " on m", k, "\n");
				fi;
			od;
		od;
	od;
end;

testAllWeyl := function()
	testLongWeylOnLong();
	testLongWeylOnShort();
	testShortWeylOnLong();
	testShortWeylOnShort();
end;

# ----- End of conjugation formulas for Weyl elements -----

testAll := function()
	testAllComm();
	testAllWeyl();
	testRootHomsPreserveQ();
	testRootHomIsHom();
end;
