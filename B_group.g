### Second file to load.
### In this file, we define the elementary orthogonal group EO(qExt).
### That is, we define the root homomorphisms, Weyl elements and the group composition.

# ---- The group EO(qExt) ----
# EO(qExt) is a subgroup of Aut(V) (in fact, of O(V)) which is generated
# by some automorphisms X_\alpha(r) (for a long root \alpha of B_n
# and r \in R) and X_\beta(v) (for a short root \beta of B_n and v \in V).
# These automorphisms are defined as follows.

# ---- Root homomorphisms -----

# X_{e_i - e_j}(r) ["pm" stands for "plus minus"]
Xpm := function(i, j, r)
	return function(modelement)
		local mpart, pospart, negpart;
		mpart := modelement[1];
		pospart := modelement[2];
		negpart := modelement[3];
		return [ mpart, pospart + r * pospart[j] * b[i],
					negpart - r * negpart[i] * b[j] ];
	end;
end;

# X_{e_i + e_j}(r)
Xpp := function(i, j, r)
	if i = j then
		return fail;
	elif i > j then
		return Xpp(j, i, r);
	else 
		return function(modelement)
			local mpart, pospart, negpart;
			mpart := modelement[1];
			pospart := modelement[2];
			negpart := modelement[3];
			return [ mpart, 
						pospart - r*negpart[i]*b[j] + r*negpart[j]*b[i],
						negpart  ];
		end;
	fi;
end;

# X_{-e_i - e_j}(r)
Xmm := function(i, j, r)
	if i = j then
		return fail;
	elif i > j then
		return Xmm(j, i, r);
	else 
		return function(modelement)
			local mpart, pospart, negpart;
			mpart := modelement[1];
			pospart := modelement[2];
			negpart := modelement[3];
			return [ mpart, pospart,
						negpart + r * pospart[i] * b[j] - r * pospart[j] * b[i] ];
		end;
	fi;
end;

# X_{e_i}(u)
Xp := function(i, u)
	return function(modelement)
		local mpart, pospart, negpart;
		mpart := modelement[1];
		pospart := modelement[2];
		negpart := modelement[3];
		return [ mpart - negpart[i] * u,
					pospart + f(u, mpart) * b[i] - negpart[i] * q(u) * b[i],
					negpart ];
	end;
end;

# X_{-e_i}(u)
Xm := function(i, u)
	return function(modelement)
		local mpart, pospart, negpart;
		mpart := modelement[1];
		pospart := modelement[2];
		negpart := modelement[3];
		return [ mpart + pospart[i] * u,
					pospart,
					negpart - f(u, mpart) * b[i] - pospart[i] * q(u) * b[i] ];
	end;
end;

# ----- End of root homomorphisms

# ----- Misc ----

idMap := Xpm(1, 2, Zero(R));

# Input: [f_1, ..., f_n]
# Output: x -> f_1(...f_n(x))
compose := function(list)
	return function(modelement)
		local l, i, result;
		result := modelement;
		l := Length(list);
		for i in [0..l-1] do
			result := list[l-i](result);
		od;
		return result;
	end;
end;

# ---- End of misc ------

# ---- Weyl elements ----

# Weyl element for e_i and v \in V such that q(v) is invertible.
# (In GAP, every indeterminate in R is (formally) invertible.)
Wp := function(i, v)
	return compose([Xm(i, -q(v)^-1 * v), Xp(i, v), Xm(i, -q(v)^-1 * v)]);
end;

# Weyl elements for e_i - e_j and r \in R such that r is invertible.
Wpm := function(i, j, r)
	return compose([Xpm(j, i, -r^-1), Xpm(i, j, r), Xpm(j, i, -r^-1)]);
end;

# ----- End of Weyl elements ---