# Undocumented because the A_n-case is rather easy. See the other types for a documentation.
n := 4;
rank := 5;
Mag := FreeGroup(rank);
xMag := GeneratorsOfGroup(Mag);
R := FreeMagmaRing(Integers, Mag);
emb := x -> ImageElm(Embedding(Mag, R), x);
xR := List(xMag, emb);

Xpm := function(i, j, a)
	local result;
	if i = j then
		return fail;
	fi;
	result := IdentityMat(n, R);
	result[i][j] := a;
	return result;
end;

Wpm := function(i, j, a)
	if i = j then
		return fail;
	else
		return Xpm(j, i, -a^-1)*Xpm(i, j, a)*Xpm(j, i, -a^-1);
	fi;
end;

testComm := function()
	local a, b, i, j, k, l, comm, result;
	a := xR[1];
	b := xR[2];
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
					comm := Xpm(i, j, -a)*Xpm(k, l, -b)*Xpm(i, j, a)*Xpm(k, l, b);
					if j = k then
						if i = l then
							continue;
						else
							result := Xpm(i, l, a*b);
						fi;
					elif i = l then
						result := Xpm(k, j, -b*a);
					else
						result := IdentityMat(n, R);
					fi;
					if comm <> result then
						Print("Problem for ", i, j, ", ", k, l, "\n");
					fi;
				od;
			od;
		od;
	od;
end;

testWeyl := function()
	local a, b, i, j, k, l, x, y, w, wInv;
	a := xR[1];
	b := xR[2];
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
					if wInv*x*w <> y then
						Print("Problem for ", i, "-", j, " on ", k, "-", l, "\n");
					fi;
				od;
			od;
		od;
	od;
end;