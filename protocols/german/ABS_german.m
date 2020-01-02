
const

  NODE_NUM : 2;
  DATA_NUM : 2;

type

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);

  ABS_NODE : union {NODE, enum{Other}};

  CACHE_STATE : enum{I,S,E};

  CACHE : record
    State : CACHE_STATE;
    Data : DATA;
  end;

  MSG_CMD : enum{Empty,ReqS,ReqE,Inv,InvAck,GntS,GntE};

  MSG : record
    Cmd : MSG_CMD;
    Data : DATA;
  end;
  new_type_0 : array [ NODE ] of CACHE;
  new_type_1 : array [ NODE ] of MSG;
  new_type_2 : array [ NODE ] of MSG;
  new_type_3 : array [ NODE ] of MSG;
  new_type_4 : array [ NODE ] of boolean;
  new_type_5 : array [ NODE ] of boolean;

var

  Cache : new_type_0;
  Chan1 : new_type_1;
  Chan2 : new_type_2;
  Chan3 : new_type_3;
  InvSet : new_type_4;
  ShrSet : new_type_5;
  ExGntd : boolean;
  CurCmd : MSG_CMD;
  CurPtr : ABS_NODE;
  MemData : DATA;
  AuxData : DATA;

ruleset  i : NODE do
rule "RecvGntE1"
  Chan2[i].Cmd = GntE
==>
begin
  Cache[i].State := E;
  Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty;
  undefine Chan2[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvGntS2"
  Chan2[i].Cmd = GntS
==>
begin
  Cache[i].State := S;
  Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty;
  undefine Chan2[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendGntE3"
  CurCmd = ReqE &
  CurPtr = i &
  Chan2[i].Cmd = Empty &
  ExGntd = false &
  forall j : NODE do
    ShrSet[j] = false
  end
==>
begin
  Chan2[i].Cmd := GntE;
  Chan2[i].Data := MemData;
  ShrSet[i] := true;
  ExGntd := true;
  CurCmd := Empty;
  undefine CurPtr;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendGntS4"
  CurCmd = ReqS &
  CurPtr = i &
  Chan2[i].Cmd = Empty &
  ExGntd = false
==>
begin
  Chan2[i].Cmd := GntS;
  Chan2[i].Data := MemData;
  ShrSet[i] := true;
  CurCmd := Empty;
  undefine CurPtr;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvInvAck5"
  Chan3[i].Cmd = InvAck &
  CurCmd != Empty &
  ExGntd = true
==>
begin
  Chan3[i].Cmd := Empty;
  ShrSet[i] := false;
  ExGntd := false;
  MemData := Chan3[i].Data;
  undefine Chan3[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvInvAck6"
  Chan3[i].Cmd = InvAck &
  CurCmd != Empty &
  ExGntd != true
==>
begin
  Chan3[i].Cmd := Empty;
  ShrSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInvAck7"
  Chan2[i].Cmd = Inv &
  Chan3[i].Cmd = Empty &
  Cache[i].State = E
==>
begin
  Chan2[i].Cmd := Empty;
  Chan3[i].Cmd := InvAck;
  Chan3[i].Data := Cache[i].Data;
  Cache[i].State := I;
  undefine Cache[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInvAck8"
  Chan2[i].Cmd = Inv &
  Chan3[i].Cmd = Empty &
  Cache[i].State != E
==>
begin
  Chan2[i].Cmd := Empty;
  Chan3[i].Cmd := InvAck;
  Cache[i].State := I;
  undefine Cache[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInv9"
  Chan2[i].Cmd = Empty &
  InvSet[i] = true &
  CurCmd = ReqE
==>
begin
  Chan2[i].Cmd := Inv;
  InvSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInv10"
  Chan2[i].Cmd = Empty &
  InvSet[i] = true &
  CurCmd = ReqS &
  ExGntd = true
==>
begin
  Chan2[i].Cmd := Inv;
  InvSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvReqE11"
  CurCmd = Empty &
  Chan1[i].Cmd = ReqE
==>
begin
  CurCmd := ReqE;
  CurPtr := i;
  Chan1[i].Cmd := Empty;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  endfor;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvReqS12"
  CurCmd = Empty &
  Chan1[i].Cmd = ReqS
==>
begin
  CurCmd := ReqS;
  CurPtr := i;
  Chan1[i].Cmd := Empty;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  endfor;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqE13"
  Chan1[i].Cmd = Empty &
  Cache[i].State = I
==>
begin
  Chan1[i].Cmd := ReqE;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqE14"
  Chan1[i].Cmd = Empty &
  Cache[i].State = S
==>
begin
  Chan1[i].Cmd := ReqE;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqS15"
  Chan1[i].Cmd = Empty &
  Cache[i].State = I
==>
begin
  Chan1[i].Cmd := ReqS;
endrule;
endruleset;

ruleset  d : DATA; i : NODE do
rule "Store16"
  Cache[i].State = E
==>
begin
  Cache[i].Data := d;
  AuxData := d;
endrule;
endruleset;

ruleset  d : DATA do
startstate
  for i : NODE do
    Chan1[i].Cmd := Empty;
    Chan2[i].Cmd := Empty;
    Chan3[i].Cmd := Empty;
    Cache[i].State := I;
    InvSet[i] := false;
    ShrSet[i] := false;
  end;
  ExGntd := false;
  CurCmd := Empty;
  MemData := d;
  AuxData := d;
endstartstate;
endruleset;

invariant "CntrlProp"
  forall i : NODE do
    forall j : NODE do
      (i != j ->
      ((Cache[i].State = E ->
      Cache[j].State = I) &
      (Cache[i].State = S ->
      (Cache[j].State = I |
      Cache[j].State = S))))
    end
  end;

invariant "DataProp"
  ((ExGntd = false ->
  MemData = AuxData) &
  forall i : NODE do
    (Cache[i].State != I ->
    Cache[i].Data = AuxData)
  end);



-- No abstract rule for rule RecvGntE1



-- No abstract rule for rule RecvGntS2


rule "ABS_SendGntE3_NODE_1"

	CurCmd = ReqE &
	CurPtr = Other &
	ExGntd = false
	& forall NODE_2 : NODE do
			ShrSet[NODE_2] = false
	end
 	& 
	forall NODE_2 : NODE do
		Chan2[NODE_2].Cmd != GntS &
		Chan2[NODE_2].Cmd != Inv &
		MemData = AuxData &
		Cache[NODE_2].State != E &
		Cache[NODE_2].State = I &
		Chan3[NODE_2].Cmd != InvAck &
		Cache[NODE_2].State != S &
		Chan3[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntE &
		InvSet[NODE_2] = false &
		Chan2[NODE_2].Cmd = Empty
	end
==>
begin
	ExGntd := true ;
	CurCmd := Empty;
endrule;
rule "ABS_SendGntS4_NODE_1"

	CurCmd = ReqS &
	CurPtr = Other &
	ExGntd = false
 	& 
	forall NODE_2 : NODE do
		Cache[NODE_2].State != E &
		Chan2[NODE_2].Cmd != Inv &
		MemData = AuxData &
		Chan3[NODE_2].Cmd != InvAck &
		Chan3[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntE
	end
==>
begin
	CurCmd := Empty;
endrule;
rule "ABS_RecvInvAck5_NODE_1"

	CurCmd != Empty &
	ExGntd = true
 	& 
	forall NODE_2 : NODE do
		Chan2[NODE_2].Cmd != GntS &
		Chan2[NODE_2].Cmd != Inv &
		Cache[NODE_2].State != E &
		Cache[NODE_2].State = I &
		ShrSet[NODE_2] = false &
		Chan3[NODE_2].Cmd != InvAck &
		Cache[NODE_2].State != S &
		Chan3[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntE &
		InvSet[NODE_2] = false &
		Chan2[NODE_2].Cmd = Empty
	end
==>
begin
	ExGntd := false ;
	MemData := AuxData;
endrule;

-- No abstract rule for rule RecvInvAck6



-- No abstract rule for rule SendInvAck7



-- No abstract rule for rule SendInvAck8



-- No abstract rule for rule SendInv9



-- No abstract rule for rule SendInv10


rule "ABS_RecvReqE11_NODE_1"

	CurCmd = Empty
 	& 
	forall NODE_2 : NODE do
		Chan2[NODE_2].Cmd != Inv &
		Cache[NODE_2].State != E &
		Chan3[NODE_2].Cmd != InvAck &
		Chan3[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntE
	end
==>
begin
	CurCmd := ReqE ;
	CurPtr := Other;
	for NODE_2 : NODE do
		InvSet[NODE_2] := ShrSet[NODE_2] ;
		;
	endfor;
endrule;
rule "ABS_RecvReqS12_NODE_1"

	CurCmd = Empty
 	& 
	forall NODE_2 : NODE do
		Chan2[NODE_2].Cmd != Inv &
		Cache[NODE_2].State != E &
		Chan3[NODE_2].Cmd != InvAck &
		Chan3[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntE
	end
==>
begin
	CurCmd := ReqS ;
	CurPtr := Other;
	for NODE_2 : NODE do
		InvSet[NODE_2] := ShrSet[NODE_2] ;
		;
	endfor;
endrule;

-- No abstract rule for rule SendReqE13



-- No abstract rule for rule SendReqE14



-- No abstract rule for rule SendReqS15



ruleset DATA_1 : DATA do
rule "ABS_Store16_NODE_1"

	forall NODE_2 : NODE do
		Chan2[NODE_2].Cmd != GntS &
		Chan2[NODE_2].Cmd != Inv &
		Cache[NODE_2].State != E &
		Cache[NODE_2].State = I &
		ShrSet[NODE_2] = false &
		Chan3[NODE_2].Cmd != InvAck &
		ExGntd = true &
		Cache[NODE_2].State != S &
		CurCmd != Empty &
		Chan3[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntE &
		InvSet[NODE_2] = false &
		Chan2[NODE_2].Cmd = Empty
	end
==>
begin
	AuxData := DATA_1;
endrule;
endruleset;