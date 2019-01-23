/* Godson-T Cache protocol for 2 memory address and 2 caches in each node */
/* The caches will take initiative in replacement while needed */
/* Locks could be nested, e.i., many locks will be acquired at the same time, however one node can only hold one lock */
/* By Kaiqiang Duan, Nov. 18, 2014 */

const
    NUM_NODE: 3;
    NUM_CACHE: 2;
    NUM_ADDR: 3;
    NUM_DATA: 3;
    NUM_LOCK: 3;

type
    TYPE_NODE: scalarset(NUM_NODE); -- 1 .. NUM_NODE;
    TYPE_CACHE: scalarset(NUM_CACHE); -- 1 .. NUM_CACHE;
    TYPE_ADDR: scalarset(NUM_ADDR); -- 1 .. NUM_ADDR;
    TYPE_DATA: scalarset(NUM_DATA);   -- 1 .. NUM_DATA;
    TYPE_LOCK: scalarset(NUM_LOCK); -- 1 .. NUM_LOCK;

    ABS_NODE : union {TYPE_NODE, enum{Other}};

    CACHE_STATE: enum{INVALID, DIRTY, VALID};
    
    CACHE: record
        state: CACHE_STATE;
        addr: TYPE_ADDR;
        data: TYPE_DATA;
    end;
    
    MEMORY: record
        data: TYPE_DATA;
    end;
    
    LOCK: record
        owner: ABS_NODE; --TYPE_NODE;
        beUsed: boolean;
        inProtection: array [TYPE_ADDR] of boolean;
    end;
    
    NODE: record
        cache: array [TYPE_CACHE] of CACHE;
        hasLock: boolean;
        firstRead: array [TYPE_ADDR] of boolean;
    end;
    
    /* assistant types */
    
    /* 
     * These are stages of that caches take initiative in replacement
     * NON: do not need Replacement
     * REQUIRE: require to replace
     * REQREPALL: in Locked First Read, need replace all dirty caches in all nodes
     * RANDOM: if there does not exist a INVALID cache, then choose a random one
     * RANDINV: if there exists at least a INVALID cache, then choose a random INVALID one
     * DESIGNATED: the cache to be replaced has been designated
     * TOREP: after DESIGNATED, if the designated cache is DIRTY, then replace it
     * DONE: the replacement has been done
     * REPALLDONE: the REQREPALL has been done
     */
    REPLACE_STAGE: enum{NON, REQUIRE, REQREPALL, RANDOM, RANDINV, DESIGNATED, TOREP, DONE, REPALLDONE};
    
    REPLACE_RULE: enum{NONE, NLNCR, NLNCW, LNCFR, LCFR, LNCNFR};
    
var
    /* modeling variables */
    memory: array [TYPE_ADDR] of MEMORY;
    lock: array [TYPE_LOCK] of LOCK;
    node: array [ABS_NODE] of NODE; -- array [TYPE_NODE] of NODE;
    /* assistant variables */
    curNode: ABS_NODE; -- TYPE_NODE;
    curCache: TYPE_CACHE;
    curMemory: TYPE_ADDR;
    curData: TYPE_DATA;
    curLock: TYPE_LOCK;
    replace: REPLACE_STAGE;
    repRule: REPLACE_RULE;
    
ruleset d: TYPE_DATA do
    startstate "Init"
        for i: TYPE_NODE do
            for j: TYPE_CACHE do
                node[i].cache[j].state := INVALID;
            endfor;
            node[i].hasLock := false;
            for a: TYPE_ADDR do
                node[i].firstRead[a] := true;
            endfor;
            curNode := i;
        endfor;
        for j: TYPE_CACHE do
            curCache := j;
        endfor;
        for a: TYPE_ADDR do
            memory[a].data := d;
            curMemory := a;
        endfor;
        curData := d;
        for l: TYPE_LOCK do
            lock[l].beUsed := false;
            curLock := l;
            for a: TYPE_ADDR do
                lock[l].inProtection[a] := false;
            endfor;
        endfor;
        replace := NON;
        repRule := NONE;
    end;
end;

/********************************** Replace ***************************************/

/* Replacement in INVALID caches (In fact, it need none replacement) */
ruleset i: TYPE_NODE do
    rule "RI"
        replace = REQUIRE &
        curNode = i &
        exists j: TYPE_CACHE do
            node[i].cache[j].state = INVALID
        endexists
    ==>
    begin
        replace := RANDINV;
    endrule;
endruleset;

/* Choose a Random INVALID Cache */
ruleset i: TYPE_NODE; j: TYPE_CACHE do
    rule "CRIC"
        replace = RANDINV &
        curNode = i &
        node[i].cache[j].state = INVALID
    ==>
    begin
        curCache := j;
        replace := DONE;
    endrule;
endruleset;

/* Replacement in None INVALID caches */
ruleset i: TYPE_NODE do
    rule "RNI"
        replace = REQUIRE &
        curNode = i &
        forall j: TYPE_CACHE do
            node[i].cache[j].state != INVALID
        endforall
    ==>
    begin
        replace := RANDOM;
    endrule;
endruleset;

/* Choose a Random Cache in all caches */
ruleset i: TYPE_CACHE do
    rule "CRC"
        replace = RANDOM
    ==>
    begin
        curCache := i;
        replace := DESIGNATED;
    endrule;
endruleset;

/* the Designated Cache is Not DIRTY */
ruleset i: TYPE_NODE; j: TYPE_CACHE do
    rule "DCND"
        replace = DESIGNATED &
        curNode = i &
        curCache = j &
        node[i].cache[j].state != DIRTY
    ==>
    begin
        replace := DONE;
    endrule;
endruleset;

/* the Designated Cache is DIRTY */
ruleset i: TYPE_NODE; j: TYPE_CACHE do
    rule "DCD"
        replace = DESIGNATED &
        curNode = i &
        curCache = j &
        node[i].cache[j].state = DIRTY
    ==>
    begin
        replace := TOREP;
    endrule;
endruleset;

/* replace */
ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR do
    rule "Replace"
        replace = TOREP &
        curNode = i &
        curCache = j &
        node[i].cache[j].addr = a
    ==>
    begin
        memory[a].data := node[i].cache[j].data;
        node[i].cache[j].state := INVALID;
        replace := DONE;
    endrule;
endruleset;

/* Require Replace All Dirty Caches in All Nodes */
ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR do
    rule "RepAll"
        replace = REQREPALL &
        node[i].cache[j].state = DIRTY &
        node[i].cache[j].addr = a
    ==>
    begin
        memory[a].data := node[i].cache[j].data;
        node[i].cache[j].state := INVALID;
    endrule;
endruleset;

/* All Dirty Caches in All Nodes have been Replaced */
rule "RepAllDone"
    replace = REQREPALL &
    forall i: TYPE_NODE; j: TYPE_CACHE do
        node[i].cache[j].state != DIRTY
    endforall
==>
begin
    replace := REPALLDONE;
end;

/********************************** No Lock Read ***********************************/

/* No Lock in Cache Read */
/* Omitted because of non-correlation to other nodes */

/* No Lock Not in Cache Read, REQUIRE replacement */
ruleset i: TYPE_NODE; a: TYPE_ADDR do
    rule "NLNCRR1"
        replace = NON &
        node[i].hasLock = false &
        forall j: TYPE_CACHE do
            node[i].cache[j].state = INVALID
        endforall
    ==>
    begin
        curNode := i;
        curMemory := a;
        replace := REQUIRE;
        repRule := NLNCR;
    endrule;
endruleset;

ruleset i: TYPE_NODE; a: TYPE_ADDR do
    rule "NLNCRR2"
        replace = NON &
        node[i].hasLock = false &
        forall j: TYPE_CACHE do
            node[i].cache[j].addr != a
        endforall
    ==>
    begin
        curNode := i;
        curMemory := a;
        replace := REQUIRE;
        repRule := NLNCR;
    endrule;
endruleset;

/* No Lock Not in Cache Read, DONE replacement */
ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR do
    rule "NLNCRD"
        replace = DONE &
        repRule = NLNCR &
        curNode = i &
        curCache = j &
        curMemory = a
    ==>
    begin
        node[i].cache[j].addr := a;
        node[i].cache[j].data := memory[a].data;
        node[i].cache[j].state := VALID;
        replace := NON;
        repRule := NONE;
    endrule;
endruleset;


/********************************** No Lock Write **********************************/

/* No Lock in Cache Write, write to cache, set state to dirty*/
ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; d: TYPE_DATA do
    rule "NLCW"
        replace = NON &
        node[i].hasLock = false &
        node[i].cache[j].state != INVALID &
        node[i].cache[j].addr = a &
        forall l: TYPE_LOCK do
            lock[l].inProtection[a] = false
        endforall
    ==>
    begin
        node[i].cache[j].data := d;
        node[i].cache[j].state := DIRTY;
    endrule;
endruleset;

/* No Lock Not in Cache Write, REQUIRE replacement */
ruleset i: TYPE_NODE; a: TYPE_ADDR; d: TYPE_DATA do
    rule "NLNCWR1"
        replace = NON &
        node[i].hasLock = false &
        forall j: TYPE_CACHE do
            node[i].cache[j].state = INVALID
        endforall &
        forall l: TYPE_LOCK do
            lock[l].inProtection[a] = false
        endforall
    ==>
    begin
        curNode := i;
        curMemory := a;
        curData := d;
        replace := REQUIRE;
        repRule := NLNCW;
    endrule;
endruleset;

ruleset i: TYPE_NODE; a: TYPE_ADDR; d: TYPE_DATA do
    rule "NLNCWR2"
        replace = NON &
        node[i].hasLock = false &
        forall j: TYPE_CACHE do
            node[i].cache[j].addr != a
        endforall &
        forall l: TYPE_LOCK do
            lock[l].inProtection[a] = false
        endforall
    ==>
    begin
        curNode := i;
        curMemory := a;
        curData := d;
        replace := REQUIRE;
        repRule := NLNCW;
    endrule;
endruleset;

/* No Lock Not in Cache Write, DONE replacement */
ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; d: TYPE_DATA do
    rule "NLNCWD"
        replace = DONE &
        repRule = NLNCW &
        curNode = i &
        curCache = j &
        curMemory = a &
        curData = d
    ==>
    begin
        node[i].cache[j].addr := a;
        node[i].cache[j].data := d;
        node[i].cache[j].state := DIRTY;
        replace := NON;
        repRule := NONE;
    endrule;
endruleset;

/************************************* Locked Read *********************************/

/* Locked in Cache First Read, REQUIRE All replacement */
ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LCFRRA"
        replace = NON &
        node[i].hasLock = true &
        lock[l].beUsed = true &
        lock[l].owner = i &
        node[i].firstRead[a] = true &
        node[i].cache[j].state != INVALID &
        node[i].cache[j].addr = a
    ==>
    begin
        curNode := i;
        curCache := j;
        curMemory := a;
        curLock := l;
        replace := REQREPALL;
        repRule := LCFR;
    endrule;
endruleset;

rule "LCFRAD"
    replace = REPALLDONE &
    repRule = LCFR
==>
begin
    replace := DESIGNATED;
end;

/* Locked in Cache First Read, DONE replacement */
ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LCFRD"
        replace = DONE &
        repRule = LCFR &
        curNode = i &
        curCache = j &
        curMemory = a &
        curLock = l
    ==>
    begin
        node[i].cache[j].data := memory[a].data;
        node[i].cache[j].state := VALID;
        node[i].firstRead[a] := false;
        lock[l].inProtection[a] := true;
        replace := NON;
        repRule := NONE;
    endrule;
endruleset;

/* Locked Not in Cache First Read, REQUIRE All replacement */
ruleset i: TYPE_NODE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LNCFRRA1"
        replace = NON &
        node[i].hasLock = true &
        lock[l].beUsed = true &
        lock[l].owner = i &
        node[i].firstRead[a] = true &
        forall j: TYPE_CACHE do
            node[i].cache[j].addr != a
        endforall
    ==>
    begin
        curNode := i;
        curMemory := a;
        curLock := l;
        replace := REQREPALL;
        repRule := LNCFR;
    endrule;
endruleset;

/* Locked Not in Cache First Read, REQUIRE All replacement */
ruleset i: TYPE_NODE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LNCFRRA2"
        replace = NON &
        node[i].hasLock = true &
        lock[l].beUsed = true &
        lock[l].owner = i &
        node[i].firstRead[a] = true &
        forall j: TYPE_CACHE do
            node[i].cache[j].addr != a
        endforall
    ==>
    begin
        curNode := i;
        curMemory := a;
        curLock := l;
        replace := REQREPALL;
        repRule := LNCFR;
    endrule;
endruleset;

rule "LNCFRAD"
    replace = REPALLDONE &
    repRule = LNCFR
==>
begin
    replace := REQUIRE;
end;

/* Locked Not in Cache First Read, DONE replacement */
ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LNCFRD"
        replace = DONE &
        repRule = LNCFR &
        curNode = i &
        curCache = j &
        curMemory = a &
        curLock = l
    ==>
    begin
        node[i].cache[j].addr := a;
        node[i].cache[j].data := memory[a].data;
        node[i].cache[j].state := VALID;
        node[i].firstRead[a] := false;
        lock[l].inProtection[a] := true;
        replace := NON;
        repRule := NONE;
    endrule;
endruleset;

/* Locked in Cache Not First Read */
/* Omitted because of non-correlation to other nodes */

/* Locked Not in Cache Not First Read, REQUIRE replacement */
ruleset i: TYPE_NODE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LNCNFRR1"
        replace = NON &
        node[i].hasLock = true &
        lock[l].beUsed = true &
        lock[l].owner = i &
        node[i].firstRead[a] = false &
        forall j: TYPE_CACHE do
            node[i].cache[j].state = INVALID
        endforall
    ==>
    begin
        curNode := i;
        curMemory := a;
        curLock := l;
        replace := REQUIRE;
        repRule := LNCNFR;
    endrule;
endruleset;

/* Locked Not in Cache Not First Read, REQUIRE replacement */
ruleset i: TYPE_NODE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LNCNFRR2"
        replace = NON &
        node[i].hasLock = true &
        lock[l].beUsed = true &
        lock[l].owner = i &
        node[i].firstRead[a] = false &
        forall j: TYPE_CACHE do
            node[i].cache[j].addr != a
        endforall
    ==>
    begin
        curNode := i;
        curMemory := a;
        curLock := l;
        replace := REQUIRE;
        repRule := LNCNFR;
    endrule;
endruleset;

/* Locked Not in Cache Not First Read, DONE replacement */
ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LNCNFRD"
        replace = DONE &
        repRule = LNCNFR &
        curNode = i &
        curCache = j &
        curMemory = a &
        curLock = l
    ==>
    begin
        node[i].cache[j].addr := a;
        node[i].cache[j].data := memory[a].data;
        node[i].cache[j].state := VALID;
        lock[l].inProtection[a] := true;
        replace := NON;
        repRule := NONE;
    endrule;
endruleset;

/************************************* Locked Write ********************************/

/* Locked in Cache Write */
ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; d: TYPE_DATA; l: TYPE_LOCK do
    rule "LCW"
        replace = NON &
        node[i].hasLock = true &
        lock[l].beUsed = true &
        lock[l].owner = i &
        node[i].cache[j].state != INVALID &
        node[i].cache[j].addr = a &
        forall m: TYPE_LOCK do
            lock[m].inProtection[a] = true -> m = l
        endforall
    ==>
    begin
        memory[a].data := d;
        node[i].cache[j].data := d;
        node[i].cache[j].state := VALID;
        lock[l].inProtection[a] := true;
    endrule;
endruleset;

/* Locked Not in Cache Write */
ruleset i: TYPE_NODE; a: TYPE_ADDR; d: TYPE_DATA; l: TYPE_LOCK do
    rule "LNCW"
        replace = NON &
        node[i].hasLock = true &
        lock[l].beUsed = true &
        lock[l].owner = i &
        forall j: TYPE_CACHE do
            node[i].cache[j].state = INVALID |
            node[i].cache[j].addr != a
        endforall &
        forall m: TYPE_LOCK do
            lock[m].inProtection[a] = true -> m = l
        endforall
    ==>
    begin
        memory[a].data := d;
        lock[l].inProtection[a] := true;
    endrule;
endruleset;

/************************************* Lock Manager ********************************/

ruleset i: TYPE_NODE; l: TYPE_LOCK do
    rule "Acquire"
        replace = NON &
        node[i].hasLock = false &
        lock[l].beUsed = false
    ==>
    begin
        lock[l].beUsed := true;
        lock[l].owner := i;
        node[i].hasLock := true;
        for j: TYPE_ADDR do
            node[i].firstRead[j] := true;
        endfor;
    endrule;
endruleset;
    
ruleset i: TYPE_NODE; l: TYPE_LOCK do
    rule "Release"
        replace = NON &
        node[i].hasLock = true &
        lock[l].beUsed = true &
        lock[l].owner = i
    ==>
    begin
        lock[l].beUsed := false;
        node[i].hasLock := false;
        for a: TYPE_ADDR do
            lock[l].inProtection[a] := false;
        endfor;
    endrule;
endruleset;

/************************************* Properties **********************************/

/* Deadlock-Free: One Node One Lock restrict */
--ruleset i: TYPE_NODE do
--    invariant "DeadlockFree"
--    (
--        replace = NON &
--        node[i].hasLock
--    ) -> (
--        exists l: TYPE_LOCK do
--            lock[l].beUsed = true &
--            lock[l].owner = i
--        endexists &
--        forall m: TYPE_LOCK; n: TYPE_LOCK do
--            m = n |
--            !lock[m].beUsed |
--            !lock[n].beUsed |
--            lock[m].owner != i |
 --           lock[n].owner != i
  --      endforall
   -- )
--end;

/* Coherence: Cached Data Equals Memory */
ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR do
    invariant "Coherence"
    (   replace = NON &
        node[i].hasLock = true &
        node[i].firstRead[a] = false &
        node[i].cache[j].state = VALID &
        node[i].cache[j].addr = a
    ) -> 
    node[i].cache[j].data = memory[a].data
end;

/************************************* Debug ***************************************/


