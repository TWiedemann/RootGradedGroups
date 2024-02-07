### Second file to load.
### In this file, we define the elementary unitary group EU(q).
### That is, we define the root homomorphisms, Weyl elements and the group composition.

# ---- The group EU(q) ----
# EU(q) is a subgroup of Aut(V) which is generated
# by some automorphisms X_\alpha(r) (for medium-length roots \alpha of BC_n
# and r \in R) and X_\beta(t) (for short roots \beta of BC_n and t \in T \subset M x R).
# These automorphisms are defined as follows.

# ---- Root homomorphisms -----

# X_{e_i - e_j}(r) ["pm" stands for "plus minus"]
Xpm := function(i, j, r)
	return function(modelement)
		local mpart, pospart, negpart;
		mpart := modelement[1];
		pospart := modelement[2];
		negpart := modelement[3];
		return [ mpart, pospart + b[i] * r * pospart[j],
					negpart - b[j] * inv(r) * negpart[i] ];
		# return [ mpart, pospart + r * pospart[j] * b[i], # Urspruenglich
					# negpart - inv(r) * negpart[i] * b[j] ];
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
						pospart + b[j]*inv(r)*negpart[i] + b[i]*r*negpart[j],
						negpart  ];
			# return [ mpart, 
						# pospart + inv(r)*negpart[i]*b[j] + r*negpart[j]*b[i],
						# negpart  ];
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
						negpart + b[j] * r * pospart[i] + b[i] * inv(r) * pospart[j] ];
			# return [ mpart, pospart,
						# negpart + r * pospart[i] * b[j] + inv(r) * pospart[j] * b[i] ];
		end;
	fi;
end;

# X_{e_i}(u)
Xp := function(i, u, t)
	return function(modelement)
		local mpart, pospart, negpart;
		mpart := modelement[1];
		pospart := modelement[2];
		negpart := modelement[3];
		return [ mpart - u * negpart[i],
					pospart - b[i] * f(u, mpart) + b[i] * t * negpart[i],
					negpart ];
		# return [ mpart - negpart[i] * u, # Urspruenglich
					# pospart + f(u, mpart) * b[i] - t * negpart[i] * b[i],
					# negpart ];
	end;
end;

# X_{-e_i}(u)
Xm := function(i, u, t)
	return function(modelement)
		local mpart, pospart, negpart;
		mpart := modelement[1];
		pospart := modelement[2];
		negpart := modelement[3];
		return [ mpart + u * pospart[i],
					pospart,
					negpart - b[i] * f(u, mpart) - b[i] * t * pospart[i] ];
		# return [ mpart + pospart[i] * u, # Urspruenglich
					# pospart,
					# negpart - f(u, mpart) * b[i] - t * pospart[i] * b[i] ];
	end;
end;

# ---- End of root homomorphisms

# ---- Misc --------

idMap := Xpm(1, 2, zeroR);

# Group multiplication on EU(q)
# Input: [f_1, ..., f_n]
# Output: x -> f_1(...(f_n(x)))
compose := function(list)
	return function(modelement)
		local i, l, result;
		l := Length(list);
		result := modelement;
		for i in [0..l-1] do
			result := list[l-i](result);
		od;
		return result;
	end;
end;

# -------------------------

# ----- Weyl elements ------

# Weyl element for e_i - e_r and invertible r \in R
Wpm := function(i, j, r)
	return compose([Xpm(j, i, -r^-1), Xpm(i, j, r), Xpm(j, i, -r^-1)]);
end;

# Inverse of Wpm(i, j, r)
WpmInv := function(i, j, r)
	return compose([Xpm(j, i, r^-1), Xpm(i, j, -r), Xpm(j, i, r^-1)]);
end;

# conjWpm(i, j, r) is the function which conjugates and element of End(V) by Wpm(i, j, r)
conjWpm := function(i, j, r)
	local w, winv;
	w := Wpm(i, j, r);
	winv := WpmInv(i, j, r);
	return function(func)
		return compose([winv, func, w]);
		# return compose([Xpm(j, i, r^-1), Xpm(i, j, -r), Xpm(j, i, r^-1), func, Xpm(j, i, -r^-1), Xpm(i, j, r), Xpm(j, i, -r^-1)]);
	end;
end;

# Weyl element for e_i and (u, t) \in T with t invertible
Wp := function(i, u, t)
	return compose([Xm(i, u * t^-1, inv(t^-1)), Xp(i, u, t), Xm(i, -u * inv(t)^-1, inv(t^-1))]);
end;

# Inverse of Wp(i, u, t)
WpInv := function(i, u, t)
	return compose([Xm(i, u * inv(t)^-1, -t^-1), Xp(i, -u, -inv(t)), Xm(i, -u * t^-1, -t^-1)]);
end;

# conjWp(i, u, t) is the function which conjugates and element of End(V) by Wp(i, u, t)
conjWp := function(i, u, t)
	return function(func)
		return compose([WpInv(i, u, t), func, Wp(i, u, t)]);
	end;
end;

# ----- End of Weyl elements ----