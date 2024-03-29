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

