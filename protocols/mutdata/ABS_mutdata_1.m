const 
    NODENUMS : 2;
	  DATANUMS: 2;
			
type 
     state : enum{I, T, C, E};

     DATA: scalarset(DATANUMS);

     status : record st:state; data: DATA; end;
     
     NODE: scalarset(NODENUMS);

var n : array [NODE] of status;

    x : boolean; 
    
    auxDATA : DATA;
    
    memDATA: DATA;
    

ruleset i : NODE do
rule "Try" 
      n[i].st = I 
==>
begin
      n[i].st := T;
endrule;endruleset;


ruleset i : NODE do
rule "Crit"
      n[i].st = T & 
      x = true 
==>
begin
      n[i].st := C;
      x := false;
      n[i].data := memDATA; 
endrule;endruleset;


ruleset i : NODE do
rule "Exit"
      n[i].st = C 
==>
begin
      n[i].st := E;
endrule;endruleset;
      
 
ruleset i : NODE do
rule "Idle"
      n[i].st = E 
==>
begin 
      n[i].st := I;
      x := true; 
      memDATA := n[i].data; 
endrule;endruleset;

ruleset i : NODE; data : DATA do rule "Store"
	n[i].st = C
==>
begin
      auxDATA := data;
      n[i].data := data; 
endrule;endruleset;    

ruleset d : DATA do 
startstate
begin
 for i: NODE do
    n[i].st := I; 
    n[i].data:=d;
  endfor;
  x := true;
  auxDATA := d;
  memDATA:=d;
endstartstate;
endruleset;


ruleset i: NODE; j: NODE do
invariant "coherence"
  i != j -> (n[i].st = C -> n[j].st != C);
endruleset;

ruleset i:NODE  do 
invariant "c51"

  (n[i].st= C -> n[i].data =auxDATA);
endruleset;


-- No abstract rule for rule Try


rule "ABS_Crit_NODE_1"

	x = true
 	& 
	forall NODE_2 : NODE do
		n[NODE_2].st = T &
		n[NODE_2].st != I &
		n[NODE_2].st != C &
		n[NODE_2].data = auxDATA &
		n[NODE_2].st != E
	end
==>
begin
	x := false;
endrule;

-- No abstract rule for rule Exit


rule "ABS_Idle_NODE_1"

	forall NODE_2 : NODE do
		x = false &
		n[NODE_2].st != C &
		n[NODE_2].st != E
	end
==>
begin
	x := true ;
	memDATA := auxDATA;
endrule;

ruleset DATA_1 : DATA do
rule "ABS_Store_NODE_1"

	forall NODE_2 : NODE do
		x = false &
		n[NODE_2].st != C &
		n[NODE_2].st != E
	end
==>
begin
	auxDATA := DATA_1;
endrule;
endruleset;



ruleset i : NODE ; j : NODE do
invariant "rule_1"
		(i != j) ->	(n[i].st = T -> n[i].st != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2"
		(i != j) ->	(x = true & n[i].st = T -> n[i].st != I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_3"
		(i != j) ->	(n[i].st = E -> n[i].st != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_4"
		(i != j) ->	(x = true & n[i].st = T -> n[i].data = auxDATA);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_5"
		(i != j) ->	(n[i].st = I -> n[i].st != C);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_6"
		(i != j) ->	(n[i].st = C -> n[i].st != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_7"
		(i != j) ->	(n[i].st = I -> n[i].st != T);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_8"
		(i != j) ->	(n[i].st = I -> n[i].st != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_9"
		(i != j) ->	(x = true & n[i].st = T -> n[i].st != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_10"
		(i != j) ->	(n[i].st = T -> n[i].data = auxDATA);
endruleset;


ruleset i : NODE do
invariant "rule_11"
	(n[i].st = E -> x = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_12"
		(i != j) ->	(n[i].st = E -> n[i].st != C);
endruleset;


ruleset i : NODE do
invariant "rule_13"
	(n[i].st = C -> x = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_14"
		(i != j) ->	(n[i].st = I -> n[i].st = I);
endruleset;


ruleset i : NODE do
invariant "rule_15"
	(n[i].st = I -> x = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_16"
		(i != j) ->	(x = true & n[i].st = T -> n[i].st != C);
endruleset;


ruleset j : NODE do
invariant "rule_17"
	(x = true -> n[j].st != C);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_18"
		(i != j) ->	(n[i].st = T -> n[i].st != C);
endruleset;


ruleset j : NODE do
invariant "rule_19"
	(x = true -> n[j].st != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_20"
		(i != j) ->	(n[i].st = C -> n[i].st != C);
endruleset;


ruleset i : NODE do
invariant "rule_21"
	(n[i].st = E -> n[i].data = auxDATA);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_22"
		(i != j) ->	(x = true & n[i].st = T -> n[i].st = T);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_23"
		(i != j) ->	(n[i].st = T -> n[i].st != I);
endruleset;
