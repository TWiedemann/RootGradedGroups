### Third file to load.
### In this file, we define various functions which verify that
### the desired commutator relations and conjugation formulas hold.
### Each test function prints an "alarm" string if some computation does not
### match the desired outcome. Otherwise it prints and returns nothing.

# ---- Auxiliary function to handle T ----

# relList = [ i_1, t_1, ..., i_k, t_k] where
# 1 <= i_l <= mod_rank, t_l \in R
# A pair [i, t] stands for the relation "f(v[i], v[i]) = t - inv(t)"
# applyRelations(relList) is the map R -> R which replaces
# all occurences of f(v[i], v[i]) by t - inv(t)
applyRelations := function(relList)
	local rel, relOnList;
	# Applies relation to element of R
	rel := function(r) # Replaces f(v, v) by t - inv(t)
		local i, modIndex, t;
		for i in [1..Length(relList)/2] do
			modIndex := relList[2*i - 1];
			t := relList[2*i];
			r := replaceR(r, [fIndetMon[modIndex][modIndex]], [t - inv(t)]);
		od;
		return r;
	end;
	# Applies relation to element of M/F_pos/F_neg
	relOnList := x -> List(x, rel);
	# Applies relation to element of V
	return x -> List(x, relOnList);
end;

# ----------------------

# ---- Equality test functions ----

# func1, func2: Functions V -> V
# relList: A list [ i_1, t_1, ..., i_k, t_k] as in "applyRelations"
# Output: true if func1 and func2 are identical modulo the relation "f(v[i_j], v[i_j]) = t_j - inv(t_j)" for all 1 <= j <= k (i.e. under the additional assumption that (v[i_j], t_j) lies in T), false otherwise.
# If the output is false, an alarm message is printed.
testEqualityModRelation := function(func1, func2, relList)
	local i, rel, relOnList, relfunc1, relfunc2, vec1, vec2;
	rel := applyRelations(relList);
	relfunc1 := x -> rel(func1(x));
	relfunc2 := x -> rel(func2(x));
	# Test equality for all basis vectors
	if relfunc1([v[mod_rank], zeroFree, zeroFree])
		<> relfunc2([v[mod_rank], zeroFree, zeroFree]) then
		Display("Inequality for v");
		return false;
	fi;
	for i in [1..n] do
		if (relfunc1([zeroM, b[i], zeroFree])
			<> relfunc2([zeroM, b[i], zeroFree])) then
			Print("Inequality for b_", i, "\n");
			return false;
		elif (relfunc1([zeroM, zeroFree, b[i]])
			<> relfunc2([zeroM, zeroFree, b[i]])) then
			Print("Inequality for b_(", -i, ")\n");
			return false;
		fi;
	od;
	return true;
end;

testEquality := function(func1, func2)
	return testEqualityModRelation(func1, func2, []);
end;

# ---- End of equality tests -------

# ----- Misc tests ------

# Tests whether short root homomorphisms are indeed homomorphisms
testShortHom := function()
	local u1, u2, t1, t2, comp, result;
	u1 := v[1];
	u2 := v[2];
	t1 := xR[1];
	t2 := xR[2];
	for i in [1..n] do
		comp := compose([Xp(i, u1, t1), Xp(i, u2, t2)]);
		result := Xp(i, u1+u2, t1 + t2 + f(u1, u2));
		if not testEqualityModRelation(comp, result, [1, t1, 2, t2]) then
			Print("Problem for ", i, "\n");
		fi;
		comp := compose([Xm(i, u1, t1), Xm(i, u2, t2)]);
		result := Xm(i, u1+u2, t1 + t2 + f(u1, u2));
		if not testEqualityModRelation(comp, result, [1, t1, 2, t2]) then
			Print("Problem for -", i, "\n");
		fi;
	od;
end;

# ----- End of misc tests -----

# ---- Commutator relations -----

# Commutators of medium-length root groups
testMidMidComm := function()
	local a1, a2, i, j, k, l, m, p, q, r, x1, x2, y1, y2, comm, result;
	a1 := xR[1];
	a2 := xR[2];
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
					x1 := Xpm(i, j, a1);
					x2 := Xpm(i, j, -a1);
					y1 := Xpm(k, l, a2);
					y2 := Xpm(k, l, -a2);
					comm := compose([x2, y2, x1, y1]);
					if j = k and i <> l then
						result := Xpm(i, l, a1*a2);
					elif i = l and j <> k then
						result := Xpm(k, j, -a2*a1);
					else
						result := idMap;
					fi;
					if not (i = l and k = j) then # do not test opposite roots
						if testEquality(comm, result) = false then
							Print("Problem for +", i, "-", j, ", +", k, "-", l, "\n");
						fi;
					fi;
					
					# [ e_i - e_j, e_k + e_l ]
					x1 := Xpm(i, j, a1);
					x2 := Xpm(i, j, -a1);
					y1 := Xpp(k, l, a2);
					y2 := Xpp(k, l, -a2);
					comm := compose([x2, y2, x1, y1]);
					if j in [k,l] then
						if i in [k,l] then
							result := Xp(i, zeroM, Tr(a1, dinv(i>j)(a2)));
						else
							# Choose m such that { j, m } = { k, l}
							if j = k then m := l;
							else m := k; fi;
							result := Xpp(i, m, dinv(m<i)(a1 * dinv(m<j)(a2)));
						fi;
					else
						result := idMap;
					fi;
					if testEquality(comm, result) = false then
						Print("Problem for +", i, "-", j, ", +", k, "+", l, "\n");
					fi;
					
					# [ e_i - e_j, -e_k - e_l ]
					x1 := Xpm(i, j, a1);
					x2 := Xpm(i, j, -a1);
					y1 := Xmm(k, l, a2);
					y2 := Xmm(k, l, -a2);
					comm := compose([x2, y2, x1, y1]);
					if i in [k,l] then
						if j in [k,l] then
							result := Xm(j, zeroM, Tr(inv(a1), dinv(j<i)(a2)));
						else
							# Choose m such that { i, m } = { k, l}
							if i = k then m := l;
							else m := k; fi;
							result := Xmm(j, m, -dinv(j<m)(inv(a1) * dinv(i<m)(a2)));
						fi;
					else
						result := idMap;
					fi;
					if testEquality(comm, result) = false then
						Print("Problem for +", i, "-", j, ", -", k, "-", l, "\n");
					fi;
					
					# [ e_i + e_j, e_k + e_l ]
					x1 := Xpp(i, j, a1);
					x2 := Xpp(i, j, -a1);
					y1 := Xpp(k, l, a2);
					y2 := Xpp(k, l, -a2);
					comm := compose([x2, y2, x1, y1]);
					result := idMap;
					if testEquality(comm, result) = false then
						Print("Problem for +", i, "+", j, ", +", k, "+", l, "\n");
					fi;
					
					# [ e_i + e_j, -e_k - e_l ]
					x1 := Xpp(i, j, a1);
					x2 := Xpp(i, j, -a1);
					y1 := Xmm(k, l, a2);
					y2 := Xmm(k, l, -a2);
					comm := compose([x2, y2, x1, y1]);
					if i in [k, l] and j in [k, l] then
						# Do nothing. There is not commutation relation for opp. roots.
					elif not i in [k, l] and not j in [k, l] then
						result := idMap;
					else
						# Choose p, q, r such that
						# [ e_i + e_j, -e_k - e_l ] = [ e_p + e_q, -e_q - e_r ]
						if i in [k, l] then
							p := j;
							q := i;
							if i = k then r := l;
							else r := k; fi;
						else
							p := i;
							q := j;
							if j = k then r := l;
							else r := k; fi;
						fi;
						result := Xpm(p, r, dinv(q<p)(a1) * dinv(q<r)(a2));
					fi;
					if not (i in [k,l] and j in [k,l]) then # do not test opposite roots
						if testEquality(comm, result) = false then
							Print("Problem for +", i, "+", j, ", -", k, "-", l, "\n");
						fi;
					fi;
					
					# [ -e_i - e_j, -e_k - e_l ]
					x1 := Xmm(i, j, a1);
					x2 := Xmm(i, j, -a1);
					y1 := Xmm(k, l, a2);
					y2 := Xmm(k, l, -a2);
					comm := compose([x2, y2, x1, y1]);
					result := idMap;
					if testEquality(comm, result) = false then
						Print("Problem for -", i, "-", j, ", -", k, "-", l, "\n");
					fi;
				od;
			od;
		od;
	od;
end;

# Commutators of short root groups
testShortShortComm := function()
	local u1, u2, t1, t2, relList, i, j, comm, commrel, x1, x2, y1, y2;
	u1 := v[1];
	u2 := v[2];
	t1 := xR[1];
	t2 := xR[2];
	relList := [1, t1, 2, t2];
	for i in [1..n] do
		for j in [1..n] do
			if i <> j then
				# [ e_i, e_j ]
				x1 := Xp(i, u1, t1);
				x2 := Xp(i, -u1, -inv(t1));
				y1 := Xp(j, u2, t2);
				y2 := Xp(j, -u2, -inv(t2));
				comm := compose([x2, y2, x1, y1]);
				if i < j then
					commrel := Xpp(i, j, f(u1, u2));
				elif i > j then
					commrel := Xpp(i, j, -f(u2, u1));
				fi;
				if testEqualityModRelation(comm, commrel, relList) = false then
					Print("Problem for +", i, ", +", j, "\n");
				fi;
				
				# [ e_i, -e_j ]
				x1 := Xp(i, u1, t1);
				x2 := Xp(i, -u1, -inv(t1));
				y1 := Xm(j, u2, t2);
				y2 := Xm(j, -u2, -inv(t2));
				comm := compose([x2, y2, x1, y1]);
				if i < j then
					commrel := Xpm(i, j, -f(u1, u2));
				elif i > j then
					commrel := Xpm(i, j, -f(u1, u2));
				fi;
				if testEqualityModRelation(comm, commrel, relList) = false then
					Print("Problem for +", i, ", -", j, "\n");
				fi;
				
				# [ -e_i, -e_j ]
				x1 := Xm(i, u1, t1);
				x2 := Xm(i, -u1, -inv(t1));
				y1 := Xm(j, u2, t2);
				y2 := Xm(j, -u2, -inv(t2));
				comm := compose([x2, y2, x1, y1]);
				if i < j then
					commrel := Xmm(i, j, f(u2, u1));
				elif i > j then
					commrel := Xmm(i, j, -f(u1, u2));
				fi;
				if testEqualityModRelation(comm, commrel, relList) = false then
					Print("Problem for -", i, ", -", j, "\n");
				fi;
			fi;
		od;
	od;
end;

# Commutators [ e_i - e_j, e_j ] etc.
testMidShortComm := function()
	local u, a, t, i, j, k, l, x1, x2, y1, y2, comm, 
			commpart1, commpart2, result, relList;
	u := v[1];
	a := xR[1];
	t := xR[2];
	relList := [1, t];
	for i in [1..n] do
		for j in [1..n] do
			if i <> j then
				for k in [1..n] do
					# [ e_i - e_j, e_k ]
					y1 := Xpm(i, j, a);
					y2 := Xpm(i, j, -a);
					x1 := Xp(k, u, t);
					x2 := Xp(k, -u, -inv(t));
					comm := compose([x2, y2, x1, y1]);
					if k = j then
						commpart1 := Xp(i, -u*inv(a), a * t * inv(a));
						commpart2 := Xpp(i, j, -dinv(i>j)(a*t));
						result := compose([commpart1, commpart2]);
					else
						result := idMap;
					fi;
					if testEqualityModRelation(comm, result, relList) = false then
						Print("Problem for +", i, "-", j, ", +", k, "\n");
					fi;
					
					# [ e_i - e_j, -e_k ]
					y1 := Xpm(i, j, a);
					y2 := Xpm(i, j, -a);
					x1 := Xm(k, u, t);
					x2 := Xm(k, -u, -inv(t));
					comm := compose([x2, y2, x1, y1]);
					if k = i then
						commpart1 := Xm(j, u*a, inv(a) * t * a);
						commpart2 := Xmm(i, j, -dinv(i>j)(inv(a)*t));
						result := compose([commpart1, commpart2]);
					else
						result := idMap;
					fi;
					if testEqualityModRelation(comm, result, relList) = false then
						Print("Problem for +", i, "-", j, ", -", k, "\n");
					fi;
					
					# [ e_i + e_j, e_k ]
					y1 := Xpp(i, j, a);
					y2 := Xpp(i, j, -a);
					x1 := Xp(k, u, t);
					x2 := Xp(k, -u, -inv(t));
					comm := compose([x2, y2, x1, y1]);
					result := idMap;
					if testEqualityModRelation(comm, result, relList) = false then
						Print("Problem for +", i, "+", j, ", +", k, "\n");
					fi;
					
					# [ e_i + e_j, -e_k ]
					y1 := Xpp(i, j, a);
					y2 := Xpp(i, j, -a);
					x1 := Xm(k, u, t);
					x2 := Xm(k, -u, -inv(t));
					comm := compose([x2, y2, x1, y1]);
					if k in [i, j] then
						# Choose l such that { i, j } = { k, l }
						if k = i then l := j;
						else l := i; fi;
						commpart1 := Xp(l, -u*dinv(k>l)(a), dinv(k<l)(a) * t * dinv(k>l)(a));
						commpart2 := Xpm(l, k, dinv(k<l)(a)*t);
						result := compose([commpart1, commpart2]);
					else
						result := idMap;
					fi;
					if testEqualityModRelation(comm, result, relList) = false then
						Print("Problem for +", i, "+", j, ", -", k, "\n");
					fi;
					
					# [ -e_i - e_j, e_k ]
					y1 := Xmm(i, j, a);
					y2 := Xmm(i, j, -a);
					x1 := Xp(k, u, t);
					x2 := Xp(k, -u, -inv(t));
					comm := compose([x2, y2, x1, y1]);
					if k in [i, j] then
						# Choose l such that { k, l } = { i, j }
						if k = i then l := j;
						else l := i; fi;
						commpart1 := Xm(l, -u*dinv(k<l)(a), dinv(k>l)(a)*t*dinv(k<l)(a));
						commpart2 := Xpm(k, l, inv(t)*dinv(k<l)(a));
						result := compose([commpart1, commpart2]);
					else
						result := idMap;
					fi;
					if testEqualityModRelation(comm, result, relList) = false then
						Print("Problem for -", i, "-", j, ", +", k, "\n");
					fi;
					
					# [ -e_i - e_j, -e_k ]
					y1 := Xmm(i, j, a);
					y2 := Xmm(i, j, -a);
					x1 := Xm(k, u, t);
					x2 := Xm(k, -u, -inv(t));
					comm := compose([x2, y2, x1, y1]);
					result := idMap;
					if testEqualityModRelation(comm, result, relList) = false then
						Print("Problem for +", i, "+", j, ", +", k, "\n");
					fi;
				od;	
			fi;
		od;
	od;
end;

# ----- End of commutator relations

# ---- Tests for conjugation formulas for Weyl elements ------

# Medium-length Weyl elements on any root group
testMidWeyl := function()
	local a, b, t, u, i, j, k, l, p, q, w, relList, conj, result;
	a := xR[1];
	b := xR[2];
	t := xR[2];
	u := v[1];
	
	for i in [1..n] do
		for j in [1..n] do
			if i = j then
				continue;
			fi;
			w := conjWpm(i, j, b);
			# On mid roots
			for k in [1..n] do
				for l in [1..n] do
					if k = l then
						continue;
					fi;
					relList := [];
					# On e_k - e_l
					conj := w(Xpm(k, l, a));
					if k in [i,j] and l in [i,j] then
						if k=i and l=j then
							result := Xpm(l, k, -b^-1*a*b^-1);
						else
							result := Xpm(l, k, -b*a*b);
						fi;
					elif k in [i,j] then
						if k = i then
							result := Xpm(j, l, b^-1*a);
						else
							result := Xpm(i, l, -b*a);
						fi;
					elif l in [i,j] then
						if l = i then
							result := Xpm(k, j, a*b);
						else
							result := Xpm(k, i, -a*b^-1);
						fi;
					else
						result := Xpm(k, l, a);
					fi;
					if testEquality(conj, result) = false then
						Print("Problem for w_(", i, "-", j, ") on +", k, "-", l, "\n");
					fi;
					
					# On e_k + e_l
					conj := w(Xpp(k, l, a));
					if k in [i,j] and l in [i,j] then
						result := Xpp(i, j, - dinv(i>j)(b*dinv(i<j)(a)*inv(b^-1))); #-b*inv(a)*inv(b^-1));
					elif k in [i,j] or l in [i, j] then
						# Choose p, q such that { p, q } = { k, l },
						# p in [i,j] and q not in [i,j]
						if k in [i,j] then
							p := k;
							q := l;
						else
							p := l;
							q := k;
						fi;
						if p = i then
							result := Xpp(j, q, dinv(q<j)(b^-1 * dinv(q<i)(a)));
						else
							result := Xpp(i, q, -dinv(q<i)(b * dinv(q<j)(a)));
						fi;
					else
						result := Xpp(k, l, a);
					fi;
					if testEquality(conj, result) = false then
						Print("Problem for w_(", i, "-", j, ") on +", k, "+", l, "\n");
					fi;
					# On -e_k - e_l
					conj := w(Xmm(k, l, a));
					if k in [i,j] and l in [i,j] then
						result := Xmm(i, j, - dinv(i>j)(inv(b) * dinv(i<j)(a) * b^-1)); # -inv(b)*inv(a)*b^-1);
					elif k in [i,j] or l in [i, j] then
						# Choose p, q such that { p, q } = { k, l },
						# p in [i,j] and q not in [i,j]
						if k in [i,j] then
							p := k;
							q := l;
						else
							p := l;
							q := k;
						fi;
						if p = i then
							result := Xmm(j, q, dinv(j<q)(inv(b) * dinv(i<q)(a)));
						else
							result := Xmm(i, q, -dinv(i<q)(inv(b^-1) * dinv(j<q)(a)));
						fi;
					else
						result := Xmm(k, l, a);
					fi;
					if testEquality(conj, result) = false then
						Print("Problem for w_(", i, "-", j, ") on -", k, "-", l, "\n");
					fi;
				od;
			od;
			# On short roots
			for k in [1..n] do
				relList := [ 1, t ];
				# On e_k
				conj := w(Xp(k, u, t));
				if k = i then
					result := Xp(j, u*inv(b^-1) , b^-1*t*inv(b^-1));
				elif k = j then
					result := Xp(i, -u*inv(b), b*t*inv(b));
				else
					result := Xp(k, u, t);
				fi;
				if testEqualityModRelation(conj, result, relList) = false then
					Print("Problem for w_(", i, "-", j, ") on +", k, "\n");
				fi;
				# On -e_k
				conj := w(Xm(k, u, t));
				if k = i then
					result := Xm(j, u*b, inv(b)*t*b);
				elif k = j then
					result := Xm(i, -u*b^-1, inv(b^-1)*t*b^-1);
				else
					result := Xm(k, u, t);
				fi;
				if testEqualityModRelation(conj, result, relList) = false then
					Print("Problem for w_(", i, "-", j, ") on -", k, "\n");
				fi;
			od;
		od;
	od;
end;

# Short Weyl elements on medium-length root groups
testShortWeylOnMid := function()
	local a, u, t, relList, symList, w, i, k, l, p, result, conj, numProblems;
	a := xR[1];
	u := v[2];
	t := xR[2];
	# t2 := oneR;
	# u2 := zeroM;
	relList := [ 2, t ];
	symList := [ ];
	numProblems := 0;
	for i in [1..n] do
		w := conjWp(i, u, t);
		for k in [1..n] do
			for l in [1..n] do
				if k = l then
					continue;
				fi;
				# On e_k - e_l
				conj := w(Xpm(k, l, a));
				if k = i then
					result := Xmm(k, l, dinv(i>l)(inv(a)*inv(t^-1)));
				elif l = i then
					result := Xpp(k, l, dinv(i<k)(a*t)); #dinv(i<k)(a*t2));
				else
					result := Xpm(k, l, a);
				fi;
				if testEqualityModRelation(conj, result, relList) = false then
					Print("Problem for w_", i, " on +", k, "-", l, "\n");
					numProblems := numProblems + 1;
				fi;
				# On e_k + e_l
				conj := w(Xpp(k, l, a));
				if i in [k,l] then
					# Choose p such that { k, l } = { p, i }
					if i = k then p := l;
					else p := k; fi;
					result := Xpm(p, i, -dinv(i<p)(a)*inv(t^-1));
				else
					result := Xpp(k, l, a);
				fi;
				if testEqualityModRelation(conj, result, relList) = false then
					Print("Problem for w_", i, " on +", k, "+", l, "\n");
					numProblems := numProblems + 1;
				fi;
				# On -e_k - e_l
				conj := w(Xmm(k, l, a));
				if i in [k,l] then
					# Choose p such that { k, l } = { p, i }
					if i = k then p := l;
					else p := k; fi;
					result := Xpm(i, p, -inv(t)*dinv(i<p)(a));
				else
					result := Xmm(k, l, a);
				fi;
				if testEqualityModRelation(conj, result, relList) = false then
					Print("Problem for w_", i, " on -", k, "-", l, "\n");
					numProblems := numProblems + 1;
				fi;
			od;
		od;
	od;
	if numProblems > 0 then
		Print("Number of problems: ", numProblems, "\n");
	fi;
end;

# Short Weyl elements on short root groups
testShortWeylOnShort := function()
	local u, t, u2, t2, w, i, j, conj, result, relList, symList;
	u := v[1];
	t := xR[1];
	u2 := v[2];
	t2 := xR[2];
	relList := [ 1, t, 2, t2 ];
	for i in [1..1] do
		w := conjWp(i, u2, t2);
		for j in [1..n] do
			# On e_j
			conj := w(Xp(j, u, t));
			if i = j then
				result := Xm(j, u*inv(t2^-1) + u2*inv(t2^-1)*f(u2, u)*inv(t2^-1), t2^-1 * t * inv(t2^-1));
			else
				result := Xp(j, u + u2*inv(t2)^-1*f(u2, u), t);
			fi;
			if testEqualityModRelation(conj, result, relList) = false then
				Print("Problem for w_", i, " on +", j, "\n");
			fi;
			
			# On -e_j
			conj := w(Xm(j, u, t));
			if i = j then
				result := Xp(j, -u*t2 - u2*inv(t2^-1)*f(u2, u)*t2, inv(t2)*t*t2);
			else
				result := Xm(j, u + u2*inv(t2)^-1*f(u2, u), t);
			fi;
			if testEqualityModRelation(conj, result, relList) = false then
				Print("Problem for w_", i, " on -", j, "\n");
			fi;
		od;
	od;
end;

# ---- End of conjugation formula tests -----

testAll := function()
	testShortHom();
	testShortShortComm();
	testMidShortComm();
	testMidMidComm();
	testMidWeyl();
	testShortWeylOnMid();
	testShortWeylOnShort();
end;