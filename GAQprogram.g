LoadPackage("rig");

# Function to construct the Generalized Alexander Quandle from "group" and "automorphism"
GeneralizedAlexanderQuandle := function(group, automorphism)
  local Fix,Q,P,QP,elems;
  
  # Function of generalized Alexander quandle in rig
  Q := HomogeneousRack(group,automorphism);
  Fix := Subgroup(group, Filtered(group, g -> automorphism(g) = g));
  elems := Elements(group);

  P := SortedList(Orbit(InnerGroup(Q), 1));
  QP := CanonicalSubrack(Q,P);
  QP.labels := P;

  P := Subgroup(group, List([1..Size(P)], i -> elems[P[i]]));
  return rec(
    size := Size(group),
    id := 0,
    Q := Q,
    G := group,
    psi := automorphism,
    Fix := Fix,
    P := P,
    QP := QP,
    ordf := Order(automorphism),
    ordFix := Size(Fix),
    idP := IdGroup(P),
    isAlex := false,
  );
end;

# Function to construct a list of classified Alexander quandles of order n
# This algorithm refers to the following:
# - W. Edwin Clark's program https://oeis.org/A193024
# - Xiang-dong Hou, Finite Modules over Z[t,t^{-1}], Journal of Knot Theory and Its RamificationsVol. 21, No. 08, 1250079 (2012)
AlexanderQuandleList := function(n)
  local nn, LCOREn, CORE, idCORE, ACORE, ACOREr, f, QCORE, PQCORE, MM, GL, G, AG, AGr, psi, flag, Q, PG, idPG, h0, h, aut, x, RESULT,SubG,flag2,H;
  RESULT:=[];
  for nn in [1..n] do
      LCOREn := AllSmallGroups(nn, IsAbelian);
      for CORE in LCOREn do
          idCORE := IdGroup(CORE);
          ACORE := AutomorphismGroup(CORE);;
          ACOREr := List(ConjugacyClasses(ACORE), Representative);
          for f in ACOREr do
              QCORE := GeneralizedAlexanderQuandle(CORE, f);
              PQCORE := QCORE.QP;
              MM := ((nn^2) / Size(PQCORE));
              if n mod MM = 0 then
                  if nn < n then
                    GL:=AllSmallGroups(n, IsAbelian);
                    for G in GL do

                      # Check if G cotains CORE as a subgroup
                      SubG:=List(ConjugacyClassesSubgroups(G),Representative);
                      if ForAny( SubG, H -> IdGroup(H) = idCORE) = false then
                          continue;
                      fi;

                      # Find psi such that h\circ f = psi|_P \circ h
                      AG := AutomorphismGroup(G);
                      AGr := List(ConjugacyClasses(AG), Representative);
                      for psi in AGr do
                          flag := 0;
                          Q := GeneralizedAlexanderQuandle(G, psi);
                          PG := Q.P;
                          idPG := IdGroup(PG);
                          if (idCORE = idPG) and (Order(psi) mod Order(f) = 0) then
                              h0 := IsomorphismGroups(CORE, PG);
                              for aut in AutomorphismGroup(PG) do
                                  h := CompositionMapping2(aut,h0);
                                  for x in CORE do
                                      if h(f(x)) <> psi(h(x)) then
                                          h := fail;
                                          break;
                                      fi;
                                  od;
                                  if h <> fail then
                                      flag := 1;
                                      Add(RESULT, Q);
                                      break;
                                  fi;
                              od;
                          fi;
                          if flag = 1 then
                              break;
                          fi;
                      od;
                      if flag = 1 then
                          break;
                      fi;
                      
                    od;
                  else
                      Add(RESULT, QCORE);
                  fi;
              fi;
          od;
      od;
  od;
  return RESULT;
end;

# Function to obtain a list of generalized Alexander quandles of order n
AllGaq := function(n)
  local Q,G,AutG,CC,psi,gaq,ret,id;

  ret := []; id := 1;

  for Q in AlexanderQuandleList(n) do
    Q.isAlex := true;
    Q.id := id; 
    id := id + 1;
    Add(ret, Q);
  od;

  for G in AllSmallGroups(n, IsAbelian,false) do
    AutG := AutomorphismGroup(G);
    for CC in ConjugacyClasses(AutG) do
      psi := Representative(CC);
      gaq := GeneralizedAlexanderQuandle(G,psi);
      gaq.id := id; 
      id := id + 1;
      Add(ret, gaq);
    od;
  od;
  return ret;
end;

# Function to construct a bijection used in the IsomorphismGaqa function (Dinic's method)
FindBijection := function(candidateList)
  local Edge,Graph,addedge,min,nV,src,tgt,INF,i,j,e,n,level,iter,que,bfs,dfs,dinic,ret;

  n := Size(candidateList);
  nV := 2*n + 2;
  src := 2*n + 1;
  tgt := 2*n + 2;
  INF := 100000;
  level := List([1..nV], i -> -1);
  iter := List([1..nV], i -> 1);

  Edge := function(rev,from,to,cap)
    return rec(
      rev := rev, from := from, to := to, cap := cap, cap_ := cap
    );
  end;
  Graph := List([1..nV], i -> []);
  addedge := function(from, to)
    Add(Graph[from], Edge(Size(Graph[to]) + 1, from, to, 1));
    Add(Graph[to], Edge(Size(Graph[from]), to, from, 0));
  end;
  min := function(a,b) 
    if a < b then return a;
    else return b; fi;
  end;

  bfs := function()
    local i,v;
    for i in [1..nV] do level[i] := -1; od;
    level[src] := 0;
    que := [];
    Add(que, src);
    while Size(que) > 0 do
      v := First(que);
      Remove(que, 1);
      for i in [1..Size(Graph[v])] do
        e := Graph[v][i];
        if(level[e.to] < 0 and e.cap > 0) then
          level[e.to] := level[v] + 1;
          Add(que, e.to);
        fi;
      od;
    od;
  end;

  dfs := function(v, f)
    local i,e,re,d;
    if v = tgt then return f; fi;
    for i in [iter[v]..Size(Graph[v])] do
      iter[v] := i;
      e := Graph[v][i];
      re := Graph[e.to][e.rev];
      if level[v] < level[e.to] and e.cap > 0 then
        d := dfs(e.to, min(f, e.cap));
        if d > 0 then
          Graph[v][i].cap := e.cap - d;
          Graph[e.to][e.rev].cap := re.cap + d;
          return d;
        fi;
      fi;
    od;
    return 0;
  end;

  dinic := function()
    local res,flow;

    res := 0;
    while true do
      bfs();
      if level[tgt] < 0 then return res; fi;
      iter := List([1..nV], i -> 1);
      flow := dfs(src, INF);
      while flow > 0 do
        res := res + flow;
        flow := dfs(src, INF);
      od;
    od;
  end;

  for i in [1..n] do
    for j in candidateList[i] do
      addedge(i, n + j.id);
    od;
  od;
  for i in [1..n] do addedge(src, i); od;
  for i in [1..n] do addedge(n + i, tgt); od;
  
  if dinic() < n then return fail; fi;
  
  ret := [];
  for i in [1..n] do
    for e in Graph[i] do
      if e.cap_ = 1 and e.cap = 0 then
        Add(ret, First(candidateList[i], j -> j.id = e.to - n).x);
      fi;
    od;
  od;
  return ret;
end;


# Function to determine the isomorphism between Q1 = Q(G,psi) and Q2 = Q(G',psi') using the main theorem in HKKK
IsomorphismGaqs := function(Q1, Q2)
  local h0,h,aut,cosets1,cosets2,elems1,elems2,A1,A2,
        ka_list,Temp,i,j,i_,j_,a,x,p,Pix,pix,pix_,dummy,id,ret;
  
  # Fix an isomorphism between P and P'. If not isomorphic, return false.
  h0 := IsomorphismGroups(Q1.P, Q2.P);
  if h0 = fail then return false; fi;

  # If Q and Q' are trivial quandles, they are obviously isomorphic.
  if InnerGroup(Q1.Q) = TrivialGroup(IsPermGroup) and 
     InnerGroup(Q2.Q) = TrivialGroup(IsPermGroup) then
    return PermList([]);
  fi;

  # Get cosets1 = P\G and cosets2 = P'\G'
  cosets1 := RightCosets(Q1.G, Q1.P);
  cosets2 := RightCosets(Q2.G, Q2.P);
  elems1 := Elements(Q1.G);
  elems2 := Elements(Q2.G);

  # A1: Fix a complete representatives for P\G
  # A2: Search for a complete representatives for P'\G' that satisfies the conditions of the main theorem in HKKK
  A1 := List(cosets1, c -> Representative(c));
  A2 := [1..Size(cosets2)]*0;

  # Search for a group isomorphism h : P -> P' that satisfies the conditions of the theorem
  for aut in AutomorphismGroup(Q2.P) do
    h := CompositionMapping(aut,h0);

    # Check the condition (A): h o psi|P = psi'|P' o h
    for x in Q1.P do
      if h(Q1.psi(x)) <> Q2.psi(h(x)) then
        h := fail;
        break;
      fi;
    od;
    if h = fail then continue; fi;
    
    # In below, check the condition (B).
    # ka_list: An array to store x in G' which are candidates for k(a) for each element a in A1.
    # For x in G', also remember the position id in P'\G' of P'x
    ka_list := [];

    # Pix: Function to create (id, x) for x in G'
    Pix := function(x)
      local id;
      id := Position(cosets2, RightCoset(Q2.P, x));
      return rec(id := id, x := x);
    end;

    # Create ka_list
    for a in A1 do
      dummy := [1..Size(cosets2)];
      Temp := [];
      for x in Q2.G do
        pix := Pix(x);
        if (h(Q1.psi(a^-1)*a) = Q2.psi(x^-1)*x) and
           (pix.id in dummy) then
          # Add(Temp.list, pix);
          Add(Temp, pix);
          dummy := Difference(dummy, [pix.id]);
        fi;
      od;
      if Size(Temp) = 0 then
        h := fail;
        break;
      fi;
      Sort(Temp, function(p1,p2)
        return p1.id < p2.id; end
      );
      Add(ka_list, Temp);
    od;
    if h = fail then continue; fi;

    A2 := FindBijection(ka_list);
    if A2 = fail then continue; fi;
    
    # If a bijection k and group isomorphism h are exists then return true.
    if A2 <> fail then return true; fi;
    
  od;
  # If a quandle isomorphism f is not found in the above search, return false
  return false;
end;

# Function to classify the list of generalized Alexander quandles by isomorphism classes
IsomorphicGaqClasses := function(gaqlist)
  local gaqlist_,compgaq,similargaq,isomgaq,
        equivclasses,equivclasses_,equiv,i,Temp,temp;
  
  gaqlist_ := ShallowCopy(gaqlist);

  # Prepare a sub function for classification

  # Comparison function for sorting using invariants
  compgaq := function(Q1, Q2)
    if Q1.ordf <> Q2.ordf then return Q1.ordf < Q2.ordf; fi;
    if Q1.ordFix <> Q2.ordFix then return Q1.ordFix < Q2.ordFix; fi;
    if Q1.idP <> Q2.idP then return Q1.idP < Q2.idP; fi;
    return false;
  end;

  # Function to sort quandles with the same invariants
  similargaq := function(Q1, Q2)
    return Q1.ordf = Q2.ordf and 
           Q1.ordFix = Q2.ordFix and 
           Q1.idP = Q2.idP;
  end;

  # Function to classify by isomorphism classes according to the main theorem
  isomgaq := function(list)
    local i,dummy,Temp,temp;

    Temp := [];
    dummy := list;
    while Size(dummy) <> 0 do
      temp := [dummy[1]];
      for i in [2..Size(dummy)] do
        if gaqlist_[dummy[1]].isAlex = true and gaqlist_[dummy[i]].isAlex = true then
          continue;
        fi;
        if IsomorphismGaqs(gaqlist_[dummy[1]], gaqlist_[dummy[i]]) 
           <> false then
          Add(temp, dummy[i]);
        fi;
      od;
      Add(Temp, temp);
      dummy := Difference(dummy, temp);
    od;
    return Temp;
  end;

  # First, classify the list by various invariants
  Sort(gaqlist_, compgaq);
  equivclasses_ := [];
  i := 1;
  while i <= Size(gaqlist_) do
    equiv := [i];
    if i = Size(gaqlist_) then
      Add(equivclasses_, equiv);
      break;
    fi;

    i := i + 1;
    while similargaq(gaqlist_[equiv[1]], gaqlist_[i]) do
      Add(equiv, i);
      if i = Size(gaqlist_) then break; fi;
      i := i + 1;
    od;
    Add(equivclasses_, equiv);
    if i = Size(gaqlist_) then 
      if not similargaq(gaqlist_[equiv[1]], gaqlist_[i]) then
        Add(equivclasses_, [i]);
      fi;
      break; 
    fi;
  od;
  
  # Further classify the list with the same invariants by using the theorem
  equivclasses := [];
  for temp in equivclasses_ do
    Temp := isomgaq(temp);
    for i in [1..Size(Temp)] do
      Add(equivclasses, Temp[i]);
    od;
  od;

  # During the sorting process, the index of each generalized Alexander quandle was changed,
  # so return it to the index of the original given list
  for temp in equivclasses do
    for i in [1..Size(temp)] do
      temp[i] := gaqlist_[temp[i]].id;
    od;
    Sort(temp);
  od;
  Sort(equivclasses);

  return equivclasses;
end;


# Output the number of isomorphism classes of generalized Alexander quandles of order n,
# the number of isomorphism classes of Alexander quandles of order n,
# and the number of isomorphism classes of connected generalized Alexander quandles of order n
file := JoinStringsWithSeparator(["GAQ.csv"],"");
PrintTo(file);
AppendTo(file, "n,#GAQ,#AQ,#Connected","\n");

for n in [1..127] do
    file_n := JoinStringsWithSeparator(["GAQ_",n],"");
    PrintTo(file_n);
    AppendTo(file_n, "# \n# computed by Jin Kosaka and Hirotake Kurihara \n# using gap 4.12.2 \n# \nGAQ_",n," :=\n[\n" );

    GaqList_ord := AllGaq (n);;
    # Classify the obtained list into isomorphism classes
    IsomClasses_ord:=IsomorphicGaqClasses(GaqList_ord);;
    countAlex:=0;
    countconnected:=0;
    for i in [1..Size(IsomClasses_ord)] do
      Qrep:=GaqList_ord[(IsomClasses_ord[i])[1]];
      
      # Express G and psi as in a permutation group
      isom1:=IsomorphismPermGroup(Qrep.G);
      G1:=Image(isom1);
      isom2:=SmallerDegreePermutationRepresentation(G1);
      G2:=Image(isom2);
      psi1:=Qrep.psi;
      psi2:=CompositionMapping(isom2,isom1, psi1,InverseGeneralMapping(isom1),InverseGeneralMapping(isom2));

      IsCon:=false;
      if IdGroup(Qrep.G)=IdGroup(Qrep.P) then
          IsCon:=true;
      fi;
      Qrec:=rec(
        G:=G2,
        psi:=psi2,
        ordFix:=Qrep.ordFix,
        ordf:=Qrep.ordf,
        isConnected:=IsCon,
        matrix:=(Qrep.Q).matrix
      );

      AppendTo(file_n, "# No.",i,"\n",Qrec,",\n");

      if Qrep.isAlex then
          countAlex:=countAlex+1;
      fi;
      if IsCon then
          countconnected:=countconnected+1;
      fi;
    od;
    AppendTo(file_n, "]; \n### end of file ###");
    Print(n,",", Size(IsomClasses_ord),",",countAlex,",",countconnected,"\n");
    AppendTo(file,n,",", Size(IsomClasses_ord),",",countAlex,",",countconnected,"\n");
od;
