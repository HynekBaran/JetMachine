# Rinvariants
#
# invariants of metrics from the Riemann tensor
# in terms of ds

#
#  A u t h o r s
#
# (c) 2016 by Michal Marvan
#
#
#  L i c e n s e
#
# Rinvariants is a free software distributed unDer the terms of the GNU General 
# Public License <http://www.gnu.org/copyleft/gpl.html> as published by 
# the Free Software Foundation.
#
# In particular, Rinvariants come with ABSOLUTELY NO WARRANTY.

#  I n i t i a l i s a t i o n
#
# spacetime(x1,x2,x3,x4); # the four spacetime coordinates
#
# initmetric(ds or M); 
#
# where
#
# [x1,x2,x3,x4] = the list of the four spacetime coordinates,
# ds = a symmetric 2-form,
# M = a 4 x 4 symmetric matrix.
#
#  G l o b a l   v a r i a b l e s
#  
# ST = the list of the four spacetime coordinates = base variables
# ds = the metric = a symmetric 2-form

# Uses Riemann.s

if map(assigned, {ttype,gym,christoffel,LeviCivita,Riemann,cderive,EinstTensor}) <> {true} then
  ERROR(`missing (unread) Riemann.s`)
fi;

d := proc(a)
  local x;
  global OS;
  if member(a, ST) then 'd'(a)
  elif vars(a) subset `b/var/s` then add(TD(a,x)*'d'(x), x = `b/var/s`)
  else 'd'(a)
  fi
end:

dcollect := proc(a) collect(a, 'd', distributed, args[2..nargs]) end:
  
metric2coeff := proc(b,i,j)
  global ST;
  if i = j then coeff(b, d(ST[i]), 2)
  else (1/2)*coeff(coeff(b, d(ST[i]), 1), d(ST[j]), 1)
  fi 
end: 

listposition := proc(a, L::list)
  local i;
  if member(a, L, i) then i else NULL fi
end:
fourprepared := false:

fourprepare := proc(fourmetric::metric, ST::list(name))
  local fourvolform,i,j,k;
  global fourprepared, invfourmetric, fourNabla, fourricci, fourRIem, fourSC, fourVOlform;
  invertmetric(invfourmetric, fourmetric);
  LeviCivita(fourNabla, fourmetric, invfourmetric, ST, TD);
  Riemann(fourRiem, fourNabla, ST, TD);
  compute(fourricci, [sub,sub], [i,j], fourRiem[k,i,k,j]);
  compute(fourSC, [], [], fourricci[i,j]*invfourmetric[i,j]);
  gym(fourRIem, [sup,sup,sub,sub], fourRiem, fourmetric, invfourmetric);
  volumeform(fourvolform, fourmetric, negative);
  gym(fourVOlform, [sup,sup,sub,sub], fourvolform, fourmetric, invfourmetric);
  fourprepared := true
end:

sixprepared := false:

sixprepare := proc()
  local pairs;
  global fourprepared, sixprepared, fourRIem, fourVOlform, sixRi, sixVo;
  pairs := [[1,2],[1,3],[1,4],[2,3],[2,4],[3,4]];
  if fourprepared = false then 
    if type(fourmetric, metric) then fourprepare(fourmetric) 
    else ERROR(`no fourmetric; call initmetric to remove this error`)
    fi
  fi;
  setattribute(sixRi, [sup,sub]);
  setattribute(sixVo, [sup,sub]);
  sixRi := matrix(6,6, proc(p,q) fourRIem[op(pairs[p]),op(pairs[q])] end);
  sixVo := matrix(6,6, proc(p,q) fourVOlform[op(pairs[p]),op(pairs[q])] end);
  sixprepared := true
end:

RRscalar := proc()
  option remember; 
  local p,q,ans;
  if sixprepared = false then sixprepare() fi;
  compute(ans, [], [], sixRi[p,q]*sixRi[q,p]);
  ans
end:

RRVscalar := proc()
  option remember; 
  local p,q,r,ans;
  if sixprepared = false then sixprepare() fi;
  compute(ans, [], [], sixRi[p,q]*sixRi[q,r]*sixVo[r,p]);
  ans
end:

RRRscalar := proc()
  option remember; 
  local p,q,r,ans;
  if sixprepared = false then sixprepare() fi;
  compute(ans, [], [], sixRi[p,q]*sixRi[q,r]*sixRi[r,p]);
  ans
end:

RRRVscalar := proc()
  option remember; 
  local p,q,r,s,ans;
  if sixprepared = false then sixprepare() fi;
  compute(ans, [], [], sixRi[p,q]*sixRi[q,r]*sixRi[r,s]*sixVo[s,p]);
  ans
end:

RVRVscalar := proc()
  option remember; 
  local p,q,r,s,ans;
  if sixprepared = false then sixprepare() fi;
  compute(ans, [], [], sixRi[p,q]*sixVo[q,r]*sixRi[r,s]*sixVo[s,p]);
  ans
end:

RRRRscalar := proc()
  option remember; 
  local p,q,r,s,ans;
  if sixprepared = false then sixprepare() fi;
  compute(ans, [], [], sixRi[p,q]*sixRi[q,r]*sixRi[r,s]*sixRi[s,p]);
  ans
end:

RRRRVscalar := proc()
  option remember; 
  local p,q,r,s,t,ans;
  if sixprepared = false then sixprepare() fi;
  compute(ans, [], [], sixRi[p,q]*sixRi[q,r]*sixRi[r,s]*sixRi[s,t]*sixVo[t,p]);
  ans
end:

RRRRRscalar := proc()
  option remember; 
  local p,q,r,s,t,ans;
  if sixprepared = false then sixprepare() fi;
  compute(ans, [], [], sixRi[p,q]*sixRi[q,r]*sixRi[r,s]*sixRi[s,t]*sixRi[t,p]);
  ans
end:



# macro(TD = TD):
















