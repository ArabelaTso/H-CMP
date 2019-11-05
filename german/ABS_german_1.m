
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
	False &
	ExGntd = false
	& forall NODE_2 : NODE do
			ShrSet[NODE_2] = false
	end
 	& 
	forall NODE_2 : NODE do
		Chan3[NODE_2].Cmd = Empty &
		Cache[NODE_2].State != S &
		Chan2[NODE_2].Cmd != GntS &
		InvSet[NODE_2] = false &
		Cache[NODE_2].State != E &
		Chan3[NODE_2].Cmd != InvAck &
		Chan2[NODE_2].Cmd != Inv &
		Cache[NODE_2].State = I &
		Chan2[NODE_2].Cmd != GntE &
		Chan2[NODE_2].Cmd = Empty &
		MemData = AuxData
	end
==>
begin
	ExGntd := true ;
	CurCmd := Empty;
endrule;
rule "ABS_SendGntS4_NODE_1"

	CurCmd = ReqS &
	False &
	ExGntd = false
 	& 
	forall NODE_2 : NODE do
		Chan3[NODE_2].Cmd = Empty &
		Cache[NODE_2].State != E &
		Chan3[NODE_2].Cmd != InvAck &
		Chan2[NODE_2].Cmd != Inv &
		Chan2[NODE_2].Cmd != GntE &
		MemData = AuxData
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
		Chan3[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntS &
		Cache[NODE_2].State = I &
		ShrSet[NODE_2] = false &
		Cache[NODE_2].State != E &
		InvSet[NODE_2] = false &
		Chan2[NODE_2].Cmd != Inv &
		Chan2[NODE_2].Cmd != GntE &
		Chan3[NODE_2].Cmd != InvAck &
		Cache[NODE_2].State != S &
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
		Chan3[NODE_2].Cmd != InvAck &
		Chan3[NODE_2].Cmd = Empty
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
		Chan3[NODE_2].Cmd != InvAck &
		Chan3[NODE_2].Cmd = Empty
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
		Chan3[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntS &
		ShrSet[NODE_2] = false &
		InvSet[NODE_2] = false &
		ExGntd = true &
		Cache[NODE_2].State != E &
		Chan2[NODE_2].Cmd != Inv &
		Cache[NODE_2].State = I &
		Chan3[NODE_2].Cmd != InvAck &
		Chan2[NODE_2].Cmd != GntE &
		Cache[NODE_2].State != S &
		Chan2[NODE_2].Cmd = Empty
	end
==>
begin
	AuxData := DATA_1;
endrule;
endruleset;


Invariant "rule_1"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntE -> Cache[NODE_2].State != S)
end;


Invariant "rule_2"
forall NODE_2 : NODE do
	(CurCmd = ReqE & ShrSet[NODE_2] = false -> Cache[NODE_2].State != E)
end;


Invariant "rule_3"
forall NODE_1 : NODE do
	(Chan3[NODE_1].Cmd = Empty & Chan2[NODE_1].Cmd = Inv -> CurCmd != Empty)
end;


Invariant "rule_4"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan3[NODE_1].Cmd = Empty -> Cache[NODE_2].State = I)
end;


Invariant "rule_5"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_6"
forall NODE_1 : NODE do
	(Chan2[NODE_1].Cmd = Inv & Cache[NODE_1].State != E -> CurCmd != Empty)
end;


Invariant "rule_7"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & ExGntd = true -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_8"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan3[NODE_1].Cmd = InvAck -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_9"
forall NODE_2 : NODE do
	(ExGntd = true & CurCmd != Empty -> Cache[NODE_2].State != S)
end;


Invariant "rule_10"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> ShrSet[NODE_2] = false)
end;


Invariant "rule_11"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan3[NODE_1].Cmd = Empty & Chan2[NODE_1].Cmd = Inv -> Cache[NODE_2].State != E)
end;


Invariant "rule_12"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(CurCmd = ReqE & InvSet[NODE_1] = true -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_13"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & ExGntd = true -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_14"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntE -> Chan2[NODE_2].Cmd = Empty)
end;


Invariant "rule_15"
forall NODE_1 : NODE do
	(Chan2[NODE_1].Cmd = Inv & Cache[NODE_1].State != E -> CurCmd = ReqE)
end;


Invariant "rule_16"
forall NODE_2 : NODE do
	(ExGntd = false & CurCmd = ReqS -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_17"
forall NODE_1 : NODE do
	(Cache[NODE_1].State = S -> MemData = AuxData)
end;


Invariant "rule_18"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & ExGntd = true -> Cache[NODE_2].State != S)
end;


Invariant "rule_19"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan1[NODE_1].Cmd = ReqE & CurCmd = Empty -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_20"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan2[NODE_1].Cmd = Empty -> Cache[NODE_2].State != S)
end;


Invariant "rule_21"
forall NODE_1 : NODE do
	(Chan2[NODE_1].Cmd = GntE -> Chan2[NODE_1].Data = AuxData)
end;


Invariant "rule_22"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan3[NODE_1].Cmd = InvAck -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_23"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan3[NODE_1].Cmd = InvAck & CurCmd != Empty -> Cache[NODE_2].State != E)
end;


Invariant "rule_24"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_25"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> Cache[NODE_2].State != E)
end;


Invariant "rule_26"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = false & Chan2[NODE_1].Cmd = Empty -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_27"
forall NODE_1 : NODE do
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> ExGntd = true)
end;


Invariant "rule_28"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & Chan2[NODE_1].Cmd = Empty -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_29"
forall NODE_2 : NODE do
	(CurCmd = ReqE & ShrSet[NODE_2] = false -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_30"
forall NODE_1 : NODE do
	(Cache[NODE_1].State = E -> ExGntd = true)
end;


Invariant "rule_31"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_32"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = Inv & Cache[NODE_1].State != E -> Cache[NODE_2].State != E)
end;


Invariant "rule_33"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntE -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_34"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false & ExGntd = false -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_35"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan3[NODE_1].Cmd = InvAck -> Cache[NODE_2].State = I)
end;


Invariant "rule_36"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntE -> ShrSet[NODE_2] = false)
end;


Invariant "rule_37"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan3[NODE_1].Cmd = Empty -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_38"
forall NODE_2 : NODE do
	(ExGntd = true & CurCmd = ReqS -> Cache[NODE_2].State != S)
end;


Invariant "rule_39"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntE -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_40"
forall NODE_1 : NODE do
	(Chan2[NODE_1].Cmd = GntS -> ExGntd = false)
end;


Invariant "rule_41"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false -> Cache[NODE_2].State != S)
end;


Invariant "rule_42"
forall NODE_2 : NODE ; NODE_1 : NODE do
	(NODE_2 != NODE_1) ->
	(ShrSet[NODE_2] = false & Chan2[NODE_1].Cmd = Empty -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_43"
forall NODE_2 : NODE do
	(CurCmd = ReqE & ExGntd = false -> Cache[NODE_2].State != E)
end;


Invariant "rule_44"
forall NODE_2 : NODE do
	(ExGntd = false & CurCmd = ReqS -> Cache[NODE_2].State != E)
end;


Invariant "rule_45"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntE -> Cache[NODE_2].State != E)
end;


Invariant "rule_46"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & CurCmd = ReqS -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_47"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & ExGntd = true -> Chan2[NODE_2].Cmd = Empty)
end;


Invariant "rule_48"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan3[NODE_1].Cmd = Empty -> Cache[NODE_2].State != E)
end;


Invariant "rule_49"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_50"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntE -> Cache[NODE_2].State = I)
end;


Invariant "rule_51"
forall NODE_2 : NODE do
	(ExGntd = false -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_52"
forall NODE_2 : NODE do
	(CurCmd = ReqE & ShrSet[NODE_2] = false -> Cache[NODE_2].State = I)
end;


Invariant "rule_53"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false -> Cache[NODE_2].State != E)
end;


Invariant "rule_54"
forall NODE_1 : NODE do
	(Cache[NODE_1].State = E & Chan3[NODE_1].Cmd = Empty -> ExGntd = true)
end;


Invariant "rule_55"
forall NODE_1 : NODE do
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> CurCmd != Empty)
end;


Invariant "rule_56"
forall NODE_2 : NODE ; NODE_1 : NODE do
	(NODE_2 != NODE_1) ->
	(ShrSet[NODE_2] = false & Chan2[NODE_1].Cmd = Empty -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_57"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = false & Chan2[NODE_1].Cmd = Empty -> Cache[NODE_2].State != E)
end;


Invariant "rule_58"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_59"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & ExGntd = true -> Cache[NODE_2].State = I)
end;


Invariant "rule_60"
forall NODE_2 : NODE do
	(ExGntd = true & CurCmd = ReqS -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_61"
forall NODE_2 : NODE do
	(CurCmd = ReqE & ShrSet[NODE_2] = false -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_62"
forall NODE_1 : NODE do
	(InvSet[NODE_1] = true & ExGntd = true -> CurCmd != Empty)
end;


Invariant "rule_63"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan3[NODE_1].Cmd = InvAck -> Cache[NODE_2].State != E)
end;


Invariant "rule_64"
forall NODE_1 : NODE do
	(Chan2[NODE_1].Cmd = Inv & Cache[NODE_1].State != E -> CurCmd != ReqS)
end;


Invariant "rule_65"
forall NODE_2 : NODE ; NODE_1 : NODE do
	(NODE_2 != NODE_1) ->
	(ShrSet[NODE_2] = false & Chan2[NODE_1].Cmd = Empty -> Cache[NODE_2].State = I)
end;


Invariant "rule_66"
forall NODE_1 : NODE do
	(Chan2[NODE_1].Cmd = GntE -> ExGntd = true)
end;


Invariant "rule_67"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & Chan2[NODE_1].Cmd = Empty -> Cache[NODE_2].State != E)
end;


Invariant "rule_68"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = Inv -> Cache[NODE_2].State != E)
end;


Invariant "rule_69"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false -> Chan2[NODE_2].Cmd = Empty)
end;


Invariant "rule_70"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & ExGntd = true -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_71"
forall NODE_2 : NODE do
	(CurCmd = ReqE & ShrSet[NODE_2] = false -> InvSet[NODE_2] = false)
end;


Invariant "rule_72"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan3[NODE_1].Cmd = InvAck -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_73"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan1[NODE_1].Cmd = ReqS & CurCmd = Empty -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_74"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan3[NODE_1].Cmd = InvAck -> Chan2[NODE_2].Cmd = Empty)
end;


Invariant "rule_75"
forall NODE_1 : NODE do
	(Chan2[NODE_1].Cmd = Inv & Cache[NODE_1].State != E -> ExGntd = false)
end;


Invariant "rule_76"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan3[NODE_1].Cmd = InvAck -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_77"
forall NODE_2 : NODE do
	(CurCmd = ReqE & ShrSet[NODE_2] = false -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_78"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & ExGntd = true -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_79"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_80"
forall NODE_2 : NODE do
	(CurCmd = ReqE & ShrSet[NODE_2] = false -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_81"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan3[NODE_1].Cmd = Empty -> ShrSet[NODE_2] = false)
end;


Invariant "rule_82"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(CurCmd = ReqE & InvSet[NODE_1] = true -> Cache[NODE_2].State != E)
end;


Invariant "rule_83"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_84"
forall NODE_1 : NODE do
	(Chan2[NODE_1].Cmd = GntS -> MemData = AuxData)
end;


Invariant "rule_85"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> Cache[NODE_2].State != S)
end;


Invariant "rule_86"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & ExGntd = true -> Cache[NODE_2].State != E)
end;


Invariant "rule_87"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntE -> InvSet[NODE_2] = false)
end;


Invariant "rule_88"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_89"
forall NODE_2 : NODE do
	(ExGntd = true & CurCmd != Empty -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_90"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan1[NODE_1].Cmd = ReqS & CurCmd = Empty -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_91"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan3[NODE_1].Cmd = InvAck & CurCmd != Empty -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_92"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> Cache[NODE_2].State = I)
end;


Invariant "rule_93"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan3[NODE_1].Cmd = InvAck -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_94"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = S -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_95"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_96"
forall NODE_2 : NODE ; NODE_1 : NODE do
	(NODE_2 != NODE_1) ->
	(ShrSet[NODE_2] = false & Chan2[NODE_1].Cmd = Empty -> InvSet[NODE_2] = false)
end;


Invariant "rule_97"
forall NODE_2 : NODE do
	(CurCmd = ReqE & ShrSet[NODE_2] = false -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_98"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false & ExGntd = false -> Cache[NODE_2].State != E)
end;


Invariant "rule_99"
forall NODE_1 : NODE do
	(Cache[NODE_1].State = S & Chan1[NODE_1].Cmd = Empty -> ExGntd = false)
end;


Invariant "rule_100"
forall NODE_2 : NODE do
	(ExGntd = true -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_101"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false & ExGntd = false -> Cache[NODE_2].State = I)
end;


Invariant "rule_102"
forall NODE_2 : NODE do
	(ExGntd = false -> Cache[NODE_2].State != E)
end;


Invariant "rule_103"
forall NODE_2 : NODE do
	(CurCmd = Empty -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_104"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_105"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan3[NODE_1].Cmd = Empty -> InvSet[NODE_2] = false)
end;


Invariant "rule_106"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = Inv & Cache[NODE_1].State != E -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_107"
forall NODE_2 : NODE do
	(CurCmd = ReqE & ExGntd = false -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_108"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan3[NODE_1].Cmd = InvAck -> Cache[NODE_2].State != E)
end;


Invariant "rule_109"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = Inv -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_110"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntS -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_111"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E -> Cache[NODE_2].State = I)
end;


Invariant "rule_112"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false & ExGntd = false -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_113"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_114"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan2[NODE_1].Cmd = Empty -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_115"
forall NODE_2 : NODE ; NODE_1 : NODE do
	(NODE_2 != NODE_1) ->
	(ShrSet[NODE_2] = false & Chan2[NODE_1].Cmd = Empty -> Chan2[NODE_2].Cmd = Empty)
end;


Invariant "rule_116"
forall NODE_2 : NODE ; NODE_1 : NODE do
	(NODE_2 != NODE_1) ->
	(ShrSet[NODE_2] = false & Chan2[NODE_1].Cmd = Empty -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_117"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E -> InvSet[NODE_2] = false)
end;


Invariant "rule_118"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & ExGntd = true -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_119"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & ExGntd = true -> ShrSet[NODE_2] = false)
end;


Invariant "rule_120"
forall NODE_1 : NODE do
	(Chan2[NODE_1].Cmd = GntE -> MemData = AuxData)
end;


Invariant "rule_121"
forall NODE_1 : NODE do
	(Cache[NODE_1].State = S & Chan1[NODE_1].Cmd = Empty -> MemData = AuxData)
end;


Invariant "rule_122"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = S & Chan1[NODE_1].Cmd = Empty -> Cache[NODE_2].State != E)
end;


Invariant "rule_123"
forall NODE_1 : NODE do
	(Chan2[NODE_1].Cmd = GntS -> Chan2[NODE_1].Data = AuxData)
end;


Invariant "rule_124"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false & ExGntd = false -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_125"
forall NODE_2 : NODE ; NODE_1 : NODE do
	(NODE_2 != NODE_1) ->
	(ShrSet[NODE_2] = false & Chan2[NODE_1].Cmd = Empty -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_126"
forall NODE_2 : NODE do
	(ExGntd = true -> Cache[NODE_2].State != S)
end;


Invariant "rule_127"
forall NODE_1 : NODE do
	(ExGntd = true & Chan3[NODE_1].Cmd = InvAck -> Chan3[NODE_1].Data = AuxData)
end;


Invariant "rule_128"
forall NODE_1 : NODE do
	(Cache[NODE_1].State = S -> ExGntd = false)
end;


Invariant "rule_129"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntE -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_130"
forall NODE_2 : NODE do
	(ExGntd = false & CurCmd = ReqS -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_131"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan3[NODE_1].Cmd = Empty -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_132"
forall NODE_2 : NODE do
	(CurCmd = ReqE & ShrSet[NODE_2] = false -> Chan2[NODE_2].Cmd = Empty)
end;


Invariant "rule_133"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E -> Chan2[NODE_2].Cmd = Empty)
end;


Invariant "rule_134"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan1[NODE_1].Cmd = ReqS & CurCmd = Empty -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_135"
(ExGntd = false -> MemData = AuxData);


Invariant "rule_136"
forall NODE_2 : NODE ; NODE_1 : NODE do
	(NODE_2 != NODE_1) ->
	(ShrSet[NODE_2] = false & Chan2[NODE_1].Cmd = Empty -> Cache[NODE_2].State != S)
end;


Invariant "rule_137"
forall NODE_2 : NODE do
	(ExGntd = false & CurCmd = ReqS -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_138"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = S -> Cache[NODE_2].State != E)
end;


Invariant "rule_139"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & CurCmd = ReqS -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_140"
forall NODE_2 : NODE ; NODE_1 : NODE do
	(NODE_2 != NODE_1) ->
	(ShrSet[NODE_2] = false & Chan2[NODE_1].Cmd = Empty -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_141"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan3[NODE_1].Cmd = InvAck -> Cache[NODE_2].State != S)
end;


Invariant "rule_142"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E -> ShrSet[NODE_2] = false)
end;


Invariant "rule_143"
forall NODE_1 : NODE do
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> Cache[NODE_1].Data = AuxData)
end;


Invariant "rule_144"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false & ExGntd = false -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_145"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan3[NODE_1].Cmd = Empty & Chan2[NODE_1].Cmd = Inv -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_146"
forall NODE_2 : NODE ; NODE_1 : NODE do
	(NODE_2 != NODE_1) ->
	(ShrSet[NODE_2] = false & Chan2[NODE_1].Cmd = Empty -> Cache[NODE_2].State != E)
end;


Invariant "rule_147"
forall NODE_1 : NODE do
	(Chan2[NODE_1].Cmd = Inv -> CurCmd != Empty)
end;


Invariant "rule_148"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false -> Cache[NODE_2].State = I)
end;


Invariant "rule_149"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false -> InvSet[NODE_2] = false)
end;


Invariant "rule_150"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false & ExGntd = false -> MemData = AuxData)
end;


Invariant "rule_151"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_152"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E -> Cache[NODE_2].State != E)
end;


Invariant "rule_153"
forall NODE_2 : NODE do
	(CurCmd = Empty -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_154"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false & ExGntd = false -> Cache[NODE_2].State != S)
end;


Invariant "rule_155"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & CurCmd = ReqS -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_156"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false & ExGntd = false -> Chan2[NODE_2].Cmd = Empty)
end;


Invariant "rule_157"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false & ExGntd = false -> InvSet[NODE_2] = false)
end;


Invariant "rule_158"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan3[NODE_1].Cmd = Empty -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_159"
forall NODE_1 : NODE do
	(Chan2[NODE_1].Cmd = Inv & Cache[NODE_1].State != E -> MemData = AuxData)
end;


Invariant "rule_160"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_161"
forall NODE_2 : NODE do
	(ShrSet[NODE_2] = false & ExGntd = false -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_162"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_163"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & ExGntd = true -> InvSet[NODE_2] = false)
end;


Invariant "rule_164"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan3[NODE_1].Cmd = Empty -> Cache[NODE_2].State != S)
end;


Invariant "rule_165"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntE -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_166"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> InvSet[NODE_2] = false)
end;


Invariant "rule_167"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan3[NODE_1].Cmd = InvAck -> ShrSet[NODE_2] = false)
end;


Invariant "rule_168"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan3[NODE_1].Cmd = InvAck -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_169"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> Chan2[NODE_2].Cmd = Empty)
end;


Invariant "rule_170"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(ExGntd = true & Chan3[NODE_1].Cmd = InvAck -> InvSet[NODE_2] = false)
end;


Invariant "rule_171"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntS -> Cache[NODE_2].State != E)
end;


Invariant "rule_172"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan2[NODE_1].Cmd = GntE -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_173"
forall NODE_2 : NODE do
	(ExGntd = false & CurCmd = ReqS -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_174"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & CurCmd = ReqS -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_175"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan1[NODE_1].Cmd = ReqE & CurCmd = Empty -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_176"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E -> Cache[NODE_2].State != S)
end;


Invariant "rule_177"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = S & Chan1[NODE_1].Cmd = Empty -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_178"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_179"
forall NODE_2 : NODE do
	(CurCmd = ReqE & ShrSet[NODE_2] = false -> Cache[NODE_2].State != S)
end;


Invariant "rule_180"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Chan1[NODE_1].Cmd = ReqE & CurCmd = Empty -> Chan3[NODE_2].Cmd != InvAck)
end;


Invariant "rule_181"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true -> Cache[NODE_2].State != E)
end;


Invariant "rule_182"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan3[NODE_1].Cmd = Empty -> Chan3[NODE_2].Cmd = Empty)
end;


Invariant "rule_183"
forall NODE_2 : NODE do
	(CurCmd = Empty -> Chan2[NODE_2].Cmd != Inv)
end;


Invariant "rule_184"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan3[NODE_1].Cmd = Empty -> Chan2[NODE_2].Cmd != GntS)
end;


Invariant "rule_185"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan2[NODE_1].Cmd = Inv -> Chan2[NODE_2].Cmd != GntE)
end;


Invariant "rule_186"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(InvSet[NODE_1] = true & CurCmd = ReqS -> Cache[NODE_2].State != E)
end;


Invariant "rule_187"
forall NODE_1 : NODE ; NODE_2 : NODE do
	(NODE_1 != NODE_2) ->
	(Cache[NODE_1].State = E & Chan3[NODE_1].Cmd = Empty -> Chan2[NODE_2].Cmd = Empty)
end;


Invariant "rule_188"
forall NODE_1 : NODE do
	(ExGntd = false & Chan2[NODE_1].Cmd = Empty -> MemData = AuxData)
end;
