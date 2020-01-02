
const

  NODE_NUM : 2;
  DATA_NUM : 2;

type

  NODE : 1..NODE_NUM;
  DATA : 1..DATA_NUM;

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


rule "n_ABS_SendGntE3_NODE_1"

	CurCmd = ReqE &
	CurPtr = Other &
	ExGntd = false
	& forall NODE_2 : NODE do
			ShrSet[NODE_2] = false
	end
 	& 
	forall NODE_2 : NODE do
		Chan2[NODE_2].Cmd != Inv &
		Chan3[NODE_2].Cmd != InvAck &
		Cache[NODE_2].State != S &
		Cache[NODE_2].State != E &
		InvSet[NODE_2] = false &
		Cache[NODE_2].State = I &
		Chan3[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntE &
		Chan2[NODE_2].Cmd != GntS &
		Chan2[NODE_2].Cmd = Empty &
		MemData = AuxData
	end
==>
begin
	ExGntd := true ;
	CurCmd := Empty;
endrule;
rule "n_ABS_SendGntS4_NODE_1"

	CurCmd = ReqS &
	CurPtr = Other &
	ExGntd = false
 	& 
	forall NODE_2 : NODE do
		Chan2[NODE_2].Cmd != Inv &
		Chan3[NODE_2].Cmd != InvAck &
		Cache[NODE_2].State != E &
		Chan3[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntE &
		MemData = AuxData
	end
==>
begin
	CurCmd := Empty;
endrule;
rule "n_ABS_RecvInvAck5_NODE_1"

	CurCmd != Empty &
	ExGntd = true
 	& 
	forall NODE_2 : NODE do
		Chan2[NODE_2].Cmd != Inv &
		Cache[NODE_2].State != S &
		Chan3[NODE_2].Cmd != InvAck &
		Cache[NODE_2].State != E &
		Cache[NODE_2].State = I &
		InvSet[NODE_2] = false &
		ShrSet[NODE_2] = false &
		Chan3[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntS &
		Chan2[NODE_2].Cmd != GntE &
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


rule "n_ABS_RecvReqE11_NODE_1"

	CurCmd = Empty
 	& 
	forall NODE_2 : NODE do
		Chan2[NODE_2].Cmd != Inv &
		Chan3[NODE_2].Cmd != InvAck &
		Cache[NODE_2].State != E &
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
rule "n_ABS_RecvReqS12_NODE_1"

	CurCmd = Empty
 	& 
	forall NODE_2 : NODE do
		Chan2[NODE_2].Cmd != Inv &
		Chan3[NODE_2].Cmd != InvAck &
		Cache[NODE_2].State != E &
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
rule "n_ABS_Store16_NODE_1"

	forall NODE_2 : NODE do
		Chan2[NODE_2].Cmd != Inv &
		Chan3[NODE_2].Cmd != InvAck &
		Cache[NODE_2].State != S &
		CurCmd != Empty &
		Cache[NODE_2].State != E &
		InvSet[NODE_2] = false &
		Cache[NODE_2].State = I &
		ShrSet[NODE_2] = false &
		Chan3[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntE &
		Chan2[NODE_2].Cmd != GntS &
		Chan2[NODE_2].Cmd = Empty &
		ExGntd = true
	end
==>
begin
	AuxData := DATA_1;
endrule;
endruleset;



ruleset i : NODE ; j : NODE do
invariant "rule_1"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_3"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_4"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_5"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_6"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_7"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_8"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_9"
	(ExGntd = false & ShrSet[j] = false -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_10"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_11"
	(ExGntd = false & CurCmd = ReqS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_12"
		(i != j) ->	(Chan2[i].Cmd = GntE -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_13"
	(ShrSet[j] = false & CurCmd = ReqE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_14"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_15"
	(Chan2[i].Cmd = Inv -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_16"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_17"
		(i != j) ->	(Cache[i].State = E -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_18"
	(ExGntd = true & CurCmd = ReqS -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
invariant "rule_19"
	(CurCmd = Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_20"
		(i != j) ->	(Chan1[i].Cmd = ReqS & CurCmd = Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_21"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
invariant "rule_22"
	(Chan1[i].Cmd = Empty & Cache[i].State = S -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_23"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_24"
		(i != j) ->	(InvSet[i] = true & Chan2[i].Cmd = Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_25"
	(ShrSet[j] = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_26"
		(i != j) ->	(Chan3[i].Cmd = Empty & Chan2[i].Cmd = Inv -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_27"
	(ExGntd = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_28"
	(ShrSet[j] = false & CurCmd = ReqE -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_29"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_30"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_31"
		(i != j) ->	(Chan1[i].Cmd = ReqS & CurCmd = Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_32"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_33"
	(ExGntd = false & ShrSet[j] = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_34"
		(i != j) ->	(Cache[i].State = E -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_35"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_36"
		(i != j) ->	(Chan1[i].Cmd = Empty & Cache[i].State = S -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_37"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_38"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_39"
		(i != j) ->	(InvSet[i] = true & Chan2[i].Cmd = Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_40"
		(i != j) ->	(InvSet[i] = true -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE do
invariant "rule_41"
	(InvSet[i] = true & ExGntd = true -> CurCmd != Empty);
endruleset;


ruleset j : NODE do
invariant "rule_42"
	(ShrSet[j] = false -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
invariant "rule_43"
	(Cache[i].State = S -> ExGntd = false);
endruleset;


ruleset j : NODE do
invariant "rule_44"
	(ExGntd = true -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_45"
		(i != j) ->	(Cache[i].State = E -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_46"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
invariant "rule_47"
	(ShrSet[j] = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_48"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_49"
		(i != j) ->	(Chan2[i].Cmd = GntE -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_50"
	(ShrSet[j] = false & CurCmd = ReqE -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
invariant "rule_51"
	(ShrSet[j] = false & CurCmd = ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
invariant "rule_52"
	(ExGntd = false & ShrSet[j] = false -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_53"
	(ExGntd = false & ShrSet[j] = false -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
invariant "rule_54"
	(ShrSet[j] = false & CurCmd = ReqE -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
invariant "rule_55"
	(CurCmd != Empty & ExGntd = true -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
invariant "rule_56"
	(CurCmd != Empty & ExGntd = true -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_57"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_58"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
invariant "rule_59"
	(Chan2[i].Cmd = GntE -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_60"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_61"
		(i != j) ->	(Chan3[i].Cmd = InvAck -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
invariant "rule_62"
	(Chan2[i].Cmd = Inv & Cache[i].State = E -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_63"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_64"
		(i != j) ->	(Cache[i].State != E & Chan2[i].Cmd = Inv -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_65"
		(i != j) ->	(Cache[i].State = S -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
invariant "rule_66"
	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan3[i].Data = AuxData);
endruleset;


ruleset i : NODE do
invariant "rule_67"
	(Chan3[i].Cmd = Empty & Chan2[i].Cmd = Inv -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_68"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_69"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_70"
	(ShrSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_71"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
invariant "rule_72"
	(ShrSet[j] = false & CurCmd = ReqE -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_73"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_74"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_75"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqE -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_76"
	(CurCmd = Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_77"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_78"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_79"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
invariant "rule_80"
	(CurCmd = Empty -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_81"
	(ExGntd = false & CurCmd = ReqS -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_82"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
invariant "rule_83"
	(ShrSet[j] = false -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_84"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_85"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE do
invariant "rule_86"
	(Cache[i].State = E -> ExGntd = true);
endruleset;


ruleset i : NODE do
invariant "rule_87"
	(Chan2[i].Cmd = Inv & Cache[i].State = E -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_88"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqE -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_89"
		(i != j) ->	(Cache[i].State = E -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_90"
	(ExGntd = false & CurCmd = ReqS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
invariant "rule_91"
	(Chan2[i].Cmd = GntS -> Chan2[i].Data = AuxData);
endruleset;


ruleset i : NODE do
invariant "rule_92"
	(Cache[i].State = E -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_93"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqE -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_94"
	(ExGntd = false & ShrSet[j] = false -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_95"
		(i != j) ->	(InvSet[i] = true -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_96"
		(i != j) ->	(Chan2[i].Cmd = Empty & ExGntd = true -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_97"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
invariant "rule_98"
	(ExGntd = true & CurCmd = ReqS -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_99"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_100"
	(ShrSet[j] = false -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
invariant "rule_101"
	(ExGntd = false & ShrSet[j] = false -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_102"
		(i != j) ->	(Chan1[i].Cmd = ReqS & CurCmd = Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_103"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_104"
	(ExGntd = false & ShrSet[j] = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_105"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
invariant "rule_106"
	(Chan3[i].Cmd = Empty & Cache[i].State = E -> CurCmd != Empty);
endruleset;


ruleset i : NODE do
invariant "rule_107"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_108"
		(i != j) ->	(Chan1[i].Cmd = ReqS & CurCmd = Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_109"
		(i != j) ->	(Chan3[i].Cmd = InvAck -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_110"
		(i != j) ->	(Cache[i].State = E -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_111"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_112"
	(ExGntd = false -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_113"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_114"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
invariant "rule_115"
	(Chan2[i].Cmd = GntS -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_116"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_117"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_118"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_119"
	(ShrSet[j] = false & CurCmd = ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_120"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
invariant "rule_121"
	(Chan2[i].Cmd = GntE -> Chan2[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_122"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_123"
		(i != j) ->	(Chan2[i].Cmd = Empty & ExGntd = true -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
invariant "rule_124"
	(CurCmd = Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_125"
		(i != j) ->	(Cache[i].State = S -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_126"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
invariant "rule_127"
	(ExGntd = false & CurCmd = ReqE -> Cache[j].State != E);
endruleset;
invariant "rule_128"
	(ExGntd = false -> MemData = AuxData);;


ruleset i : NODE do
invariant "rule_129"
	(ExGntd = false & Chan2[i].Cmd = Empty -> MemData = AuxData);
endruleset;


ruleset j : NODE do
invariant "rule_130"
	(ExGntd = false & CurCmd = ReqS -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_131"
	(ShrSet[j] = false & CurCmd = ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_132"
		(i != j) ->	(Chan1[i].Cmd = Empty & Cache[i].State = S -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
invariant "rule_133"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_134"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_135"
		(i != j) ->	(ExGntd = false & Chan2[i].Cmd = Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_136"
	(CurCmd = Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_137"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqS -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_138"
		(i != j) ->	(Cache[i].State != E & Chan2[i].Cmd = Inv -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_139"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_140"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
invariant "rule_141"
	(ExGntd = false & ShrSet[j] = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_142"
	(ExGntd = false & ShrSet[j] = false -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_143"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_144"
		(i != j) ->	(ExGntd = false & Chan2[i].Cmd = Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_145"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_146"
		(i != j) ->	(Cache[i].State = E -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
invariant "rule_147"
	(ShrSet[j] = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_148"
		(i != j) ->	(Chan2[i].Cmd = Inv -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_149"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_150"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan2[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_151"
	(ShrSet[j] = false & CurCmd = ReqE -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
invariant "rule_152"
	(Chan3[i].Cmd = Empty & Cache[i].State = E -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_153"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_154"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_155"
	(ExGntd = false & CurCmd = ReqE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_156"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_157"
	(ExGntd = false & ShrSet[j] = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_158"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_159"
		(i != j) ->	(Chan2[i].Cmd = Empty & ShrSet[i] = false -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_160"
		(i != j) ->	(Chan2[i].Cmd = Inv -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
invariant "rule_161"
	(ShrSet[j] = false -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
invariant "rule_162"
	(ExGntd = false & ShrSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_163"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_164"
	(Chan3[i].Cmd = Empty & Chan2[i].Cmd = Inv -> Cache[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_165"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_166"
	(ShrSet[j] = false -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
invariant "rule_167"
	(ExGntd = true -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_168"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
invariant "rule_169"
	(Chan2[i].Cmd = GntS -> MemData = AuxData);
endruleset;


ruleset i : NODE do
invariant "rule_170"
	(Chan1[i].Cmd = Empty & Cache[i].State = S -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_171"
		(i != j) ->	(Cache[i].State = E -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
invariant "rule_172"
	(Chan2[i].Cmd = GntE -> MemData = AuxData);
endruleset;


ruleset i : NODE do
invariant "rule_173"
	(Chan2[i].Cmd = GntE -> CurCmd != Empty);
endruleset;


ruleset j : NODE do
invariant "rule_174"
	(ExGntd = false & CurCmd = ReqS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_175"
		(i != j) ->	(Cache[i].State = E -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_176"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_177"
		(i != j) ->	(Chan1[i].Cmd = ReqS & CurCmd = Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_178"
		(i != j) ->	(Cache[i].State = E -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_179"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_180"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_181"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_182"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_183"
		(i != j) ->	(Chan3[i].Cmd = Empty & Chan2[i].Cmd = Inv -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_184"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_185"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_186"
		(i != j) ->	(InvSet[i] = true & ExGntd = true -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
invariant "rule_187"
	(ShrSet[j] = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_188"
		(i != j) ->	(Cache[i].State = E -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_189"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_190"
		(i != j) ->	(InvSet[i] = true & CurCmd = ReqS -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_191"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_192"
		(i != j) ->	(Cache[i].State = E -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_193"
		(i != j) ->	(Chan3[i].Cmd = Empty & Cache[i].State = E -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_194"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[i].State = E -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_195"
		(i != j) ->	(Chan3[i].Cmd = InvAck & ExGntd = true -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
invariant "rule_196"
	(ShrSet[j] = false & CurCmd = ReqE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
invariant "rule_197"
	(Cache[i].State = S -> MemData = AuxData);
endruleset;
