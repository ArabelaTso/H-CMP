const 
      NODENUMS : 2;
type 
     location: enum{ M, E, S, I};

     NODE : 1..NODENUMS;
    ABS_NODE : union {NODE, enum{Other}};

var 
    state : array [NODE] of location;

    
ruleset i : NODE do rule "t1"
    state[i] = E ==>
begin
    state[i]  :=  M;
    endrule; endruleset;

      
ruleset i : NODE do rule "t2"
    state[i] = I ==>
begin
  for j: NODE do
      if (j = i) then
        state[j] := S;
      elsif (state[j]=E) then
        state[j] := S;
      elsif (state[j]=M) then
        state[j] := S;
      elsif (state[j]=I) then
        state[j] := I;
      else   
        state[j] := S;
      endif;
  endfor; 
endrule;endruleset;
          

ruleset i : NODE 
do rule "t3"
      state[i] = S ==>
begin
  for j: NODE do
    if (j = i) then
      state[j] := E;
    else   
      state[j] := I;
    endif;
    endfor; 
endrule;endruleset;
      

ruleset i : NODE do rule "t4"
  state[i] = M
==>
begin
  for j: NODE do
      if (j = i) then
            state[j] := E ;
      else   
            state[j] := I;
      endif;
  endfor; 
endrule;
endruleset;

startstate
begin
 for i: NODE do
    state[i]  :=  I; 
  endfor; 
endstartstate;

invariant "Mesi"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (state[i] = M -> state[j] != M
)
 end  end ;


-- No abstract rule for rule t1


rule "n_ABS_t2_NODE_1"

	forall NODE_2 : NODE do
		state[NODE_2] != M &
		state[NODE_2] != E &
		state[NODE_2] != S &
		state[NODE_2] = I
	end
==>
begin
	for NODE_2 : NODE do
		if (NODE_2 = Other) then
        state[NODE_2] := S ;
		elsif (state[NODE_2]=E) then
        state[NODE_2] := S ;
		elsif (state[NODE_2]=M) then
        state[NODE_2] := S ;
		elsif (state[NODE_2]=I) then
        state[NODE_2] := I ;
		else   
        state[NODE_2] := S ;
		endif
 ;
	endfor;
endrule;
rule "n_ABS_t3_NODE_1"

	forall NODE_2 : NODE do
		state[NODE_2] != M &
		state[NODE_2] != E &
		state[NODE_2] = S &
		state[NODE_2] != I
	end
==>
begin
	for NODE_2 : NODE do
		if (NODE_2 = Other) then
      state[NODE_2] := E ;
		else   
      state[NODE_2] := I ;
		endif
 ;
	endfor;
endrule;
rule "n_ABS_t4_NODE_1"

	forall NODE_2 : NODE do
		state[NODE_2] != M &
		state[NODE_2] != E &
		state[NODE_2] != S &
		state[NODE_2] = I
	end
==>
begin
	for NODE_2 : NODE do
		if (NODE_2 = Other) then
            state[NODE_2] := E ;
		else   
            state[NODE_2] := I ;
		endif
 ;
	endfor;
endrule;

ruleset i : NODE ; j : NODE do
invariant "rule_1"
		(i != j) ->	(state[i] = E -> state[i] != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2"
		(i != j) ->	(state[i] = I -> state[i] = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_3"
		(i != j) ->	(state[i] = S -> state[i] != I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_4"
		(i != j) ->	(state[i] = S -> state[i] != M);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_5"
		(i != j) ->	(state[i] = M -> state[i] != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_6"
		(i != j) ->	(state[i] = I -> state[i] != M);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_7"
		(i != j) ->	(state[i] = I -> state[i] != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_8"
		(i != j) ->	(state[i] = M -> state[i] != M);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_9"
		(i != j) ->	(state[i] = E -> state[i] != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_10"
		(i != j) ->	(state[i] = M -> state[i] = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_11"
		(i != j) ->	(state[i] = I -> state[i] != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_12"
		(i != j) ->	(state[i] = M -> state[i] != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_13"
		(i != j) ->	(state[i] = S -> state[i] = S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_14"
		(i != j) ->	(state[i] = E -> state[i] != M);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_15"
		(i != j) ->	(state[i] = S -> state[i] != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_16"
		(i != j) ->	(state[i] = E -> state[i] = I);
endruleset;
