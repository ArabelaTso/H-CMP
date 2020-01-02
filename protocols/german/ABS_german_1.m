
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


ruleset i : NODE do
invariant "rule_1"
	(Cache[i].State = S & Chan1[i].Cmd = Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_3"
		(i != j) ->	(Cache[i].State != E & Chan2[i].Cmd = Inv -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_4"
		(i != j) ->	(Chan2[i].Cmd = Inv -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_5"
		(i != j) ->	(Cache[i].State = S -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_6"
	(ExGntd = true & CurCmd != Empty -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_7"
		(i != j) ->	(Chan2[i].Cmd = Empty & ExGntd = true -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_8"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_9"
		(i != j) ->	(Cache[i].State = S -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
invariant "rule_10"
	(Cache[i].State = S -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_11"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_12"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_13"
	(ShrSet[j] = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_14"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_15"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_16"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_17"
	(ShrSet[j] = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_18"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_19"
		(i != j) ->	(Cache[i].State = E -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_20"
		(i != j) ->	(InvSet[i] = true & Chan2[i].Cmd = Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_21"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqE -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_22"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqE -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_23"
		(i != j) ->	(Cache[i].State = E -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
invariant "rule_24"
	(ExGntd = false & ShrSet[j] = false -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_25"
		(i != j) ->	(Chan2[i].Cmd = GntE -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_26"
	(Chan2[i].Cmd = GntE -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_27"
		(i != j) ->	(InvSet[i] = true & Chan2[i].Cmd = Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_28"
		(i != j) ->	(Cache[i].State = E -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_29"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_30"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_31"
		(i != j) ->	(Chan2[i].Cmd = Empty & ExGntd = false -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE do
invariant "rule_32"
	(InvSet[i] = true & ExGntd = true -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_33"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
invariant "rule_34"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_35"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_36"
		(i != j) ->	(Cache[i].State = S & Chan1[i].Cmd = Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_37"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_38"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_39"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_40"
	(ExGntd = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
invariant "rule_41"
	(Chan2[i].Cmd = GntS -> ExGntd = false);
endruleset;


ruleset j : NODE do
invariant "rule_42"
	(ExGntd = true -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_43"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_44"
		(i != j) ->	(Cache[i].State = E -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_45"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
invariant "rule_46"
	(Chan2[i].Cmd = Inv -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_47"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqS -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_48"
		(i != j) ->	(Chan3[i].Cmd = Empty & Chan2[i].Cmd = Inv -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_49"
	(CurCmd = ReqE & ExGntd = false -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_50"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_51"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_52"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_53"
		(i != j) ->	(Cache[i].State = E -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_54"
		(i != j) ->	(Cache[i].State = E -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_55"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE do
invariant "rule_56"
	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Cache[i].Data = AuxData);
endruleset;


ruleset j : NODE do
invariant "rule_57"
	(ShrSet[j] = false -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_58"
		(i != j) ->	(Chan3[i].Cmd = Empty & Chan2[i].Cmd = Inv -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_59"
	(CurCmd = ReqS & ExGntd = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
invariant "rule_60"
	(Chan2[i].Cmd = GntS -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_61"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_62"
	(CurCmd = ReqE & ExGntd = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_63"
	(ExGntd = false & ShrSet[j] = false -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_64"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
invariant "rule_65"
	(ShrSet[j] = false -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_66"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
invariant "rule_67"
	(ShrSet[j] = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_68"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_69"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqS -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_70"
	(ExGntd = false & ShrSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_71"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
invariant "rule_72"
	(ExGntd = false & ShrSet[j] = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_73"
	(Cache[i].State = E -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_74"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_75"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_76"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_77"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_78"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_79"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqS -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_80"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_81"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
invariant "rule_82"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> MemData = AuxData);
endruleset;


ruleset j : NODE do
invariant "rule_83"
	(CurCmd = Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_84"
	(Cache[i].State = S -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_85"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
invariant "rule_86"
	(Cache[i].State = E -> ExGntd = true);
endruleset;


ruleset j : NODE do
invariant "rule_87"
	(CurCmd = ReqE & ShrSet[j] = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_88"
	(CurCmd = ReqE & ShrSet[j] = false -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_89"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_90"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_91"
		(i != j) ->	(Chan2[i].Cmd = Empty & ExGntd = false -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_92"
	(ExGntd = false & ShrSet[j] = false -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_93"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_94"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqS -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_95"
	(CurCmd = ReqE & ShrSet[j] = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_96"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_97"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
invariant "rule_98"
	(Chan3[i].Cmd = Empty & Cache[i].State = E -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_99"
		(i != j) ->	(Cache[i].State = E -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_100"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
invariant "rule_101"
	(CurCmd = Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
invariant "rule_102"
	(ExGntd = false & ShrSet[j] = false -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
invariant "rule_103"
	(ExGntd = false & ShrSet[j] = false -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_104"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_105"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_106"
	(CurCmd = ReqS & ExGntd = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_107"
	(ExGntd = true & CurCmd != Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
invariant "rule_108"
	(CurCmd = Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_109"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_110"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_111"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_112"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_113"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_114"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_115"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_116"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_117"
	(ExGntd = false & ShrSet[j] = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_118"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_119"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_120"
	(CurCmd = ReqE & ShrSet[j] = false -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_121"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_122"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_123"
	(ShrSet[j] = false -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
invariant "rule_124"
	(CurCmd = ReqS & ExGntd = false -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_125"
	(ExGntd = true -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
invariant "rule_126"
	(Chan2[i].Cmd = Inv & Cache[i].State = E -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_127"
		(i != j) ->	(InvSet[i] = true -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_128"
	(ShrSet[j] = false -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_129"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
invariant "rule_130"
	(CurCmd = ReqS & ExGntd = true -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
invariant "rule_131"
	(Chan2[i].Cmd = GntE -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_132"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
invariant "rule_133"
	(Chan3[i].Cmd = Empty & Chan2[i].Cmd = Inv -> CurCmd != Empty);
endruleset;


ruleset j : NODE do
invariant "rule_134"
	(CurCmd = ReqS & ExGntd = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
invariant "rule_135"
	(ShrSet[j] = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_136"
	(CurCmd = ReqE & ShrSet[j] = false -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_137"
	(ExGntd = false & ShrSet[j] = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_138"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
invariant "rule_139"
	(ShrSet[j] = false -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_140"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_141"
		(i != j) ->	(Cache[i].State = E -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_142"
		(i != j) ->	(Chan2[i].Cmd = Empty & ExGntd = true -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_143"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_144"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_145"
		(i != j) ->	(Chan3[i].Cmd = InvAck -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_146"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_147"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_148"
	(CurCmd = ReqS & ExGntd = true -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
invariant "rule_149"
	(Chan3[i].Cmd = Empty & Cache[i].State = E -> CurCmd != Empty);
endruleset;


ruleset i : NODE do
invariant "rule_150"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
invariant "rule_151"
	(CurCmd = ReqE & ShrSet[j] = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
invariant "rule_152"
	(Chan2[i].Cmd = GntE -> Chan2[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_153"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_154"
	(CurCmd = ReqE & ShrSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
invariant "rule_155"
	(Chan2[i].Cmd = Inv & Cache[i].State = E -> ExGntd = true);
endruleset;


ruleset j : NODE do
invariant "rule_156"
	(CurCmd = Empty -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_157"
	(ExGntd = false & ShrSet[j] = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_158"
	(CurCmd = ReqS & ExGntd = false -> Chan2[j].Cmd != Inv);
endruleset;
invariant "rule_159"
	(ExGntd = false -> MemData = AuxData);;


ruleset j : NODE do
invariant "rule_160"
	(ExGntd = false -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_161"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
invariant "rule_162"
	(ShrSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_163"
		(i != j) ->	(Chan2[i].Cmd = GntE -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_164"
	(ExGntd = false & ShrSet[j] = false -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_165"
		(i != j) ->	(Chan2[i].Cmd = Inv -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_166"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_167"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_168"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqE -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_169"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_170"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_171"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
invariant "rule_172"
	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan3[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_173"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_174"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_175"
		(i != j) ->	(InvSet[i] = true -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_176"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_177"
	(CurCmd = Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_178"
		(i != j) ->	(Cache[i].State = E -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
invariant "rule_179"
	(Chan2[i].Cmd = GntE -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_180"
		(i != j) ->	(Cache[i].State = E -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
invariant "rule_181"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_182"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
invariant "rule_183"
	(Chan2[i].Cmd = GntS -> Chan2[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_184"
		(i != j) ->	(Cache[i].State = E -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_185"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_186"
	(CurCmd = ReqE & ShrSet[j] = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_187"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
invariant "rule_188"
	(CurCmd = ReqE & ShrSet[j] = false -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_189"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_190"
		(i != j) ->	(Chan3[i].Cmd = InvAck -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
invariant "rule_191"
	(Cache[i].State = S & Chan1[i].Cmd = Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_192"
		(i != j) ->	(Cache[i].State != E & Chan2[i].Cmd = Inv -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_193"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_194"
		(i != j) ->	(Cache[i].State = S & Chan1[i].Cmd = Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE do
invariant "rule_195"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset j : NODE do
invariant "rule_196"
	(CurCmd = ReqE & ShrSet[j] = false -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
invariant "rule_197"
	(Chan2[i].Cmd = Empty & ExGntd = false -> MemData = AuxData);
endruleset;
