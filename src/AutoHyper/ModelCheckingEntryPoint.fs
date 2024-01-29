(*    
    Copyright (C) 2022-2023 Raven Beutner

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

module ModelCheckingEntryPoint

open System
open System.IO
open System.Collections.Generic
open FsOmegaLib.LTL
open FsOmegaLib.NBA
open FsOmegaLib.Operations
open FsOmegaLib.SAT

open TransitionSystemLib.TransitionSystem
open TransitionSystemLib.SymbolicSystem
open TransitionSystemLib.BooleanProgramSystem

open RunConfiguration
open HyperLTL
open HyperLTL.SymbolicHyperLTL
open ModelChecking


type Record = list <(int * int * DNF<int>)>

let private string_of_set_elements (list: Set<int>)  =
    list 
        |> Set.map (fun x -> string x)
        |> Set.toList
        |> Util.combineStringsWithSeperator " "

let private findNextStatesFromTransitionSystem 
    (ts : TransitionSystem<String>)  
    (current: Set<int>) : 
    Set <Set<int> * Set<int>> 
    =  (* return: a set of transitions, each transition is a pair (successors, and AP) where both of them are Set<int> *)
    let mutable NextStates = Set.empty 
    for s in ts.States do
        //printfn "current * s: %s, %d" (string_of_set_elements current ) s
        if Set.exists (fun i -> i = s) current then 
            let (sucs:Set<int>) = ts.Edges.[s]
            let (apEval:Set<int>) = ts.ApEval.[s]
            NextStates <- NextStates.Add (sucs, apEval)                
        else ()  
    NextStates



let private findNextStatesFromNBA 
    (nba : NBA<int, (String * int)>) 
    (current: Set<int>) : 
    Set<(DNF<int> * int) list>
    =  (* return: a set of transitions, each transition is a pair (dnf, and successor) where successor is a single state *)
    let mutable NextStates = Set.empty 
    for s in nba.States do
        if Set.exists (fun i -> i = s) current then 
            let (sucs: (DNF<int> * int) list) = nba.Edges.[s]
            // for (g, n') in sucs do 
            NextStates <- NextStates.Add sucs
              //  s.WriteLine("[" + DNF.print g + "] " + stateStringer(n')) 
        else ()  
    NextStates


let private existRecord 
    (memorization:Dictionary<int, (Set<int> * Set<int> * int * DNF<int>)>) 
    (currentProduct: (Set<int> * Set<int> * int * DNF<int>)) =
    let (systemStates, _, nbaState, _) = currentProduct
    let length = memorization.Count - 1
    let mutable Return = false 

    for i in 0 .. length do 

        let (csys, _, cnba, _) = memorization[i]
        //printfn "csys %s" (string_of_set_elements systemStates)
        //printfn "cnba %s" (string_of_set_elements nbaStates)
        if Set.isSubset systemStates csys && nbaState = cnba then 
            Return <- true 
        else ()

    Return

let rec recordReoccur 
    (history:Record) 
    (currentProduct: (int * int)) : bool =
    let (systemStates, nbaState) = currentProduct
    match history with 
    | [] -> false 
    | (his_sys, his_nba, _)::tail -> 
        if his_sys = systemStates && his_nba = nbaState then true 
        else recordReoccur tail currentProduct




let rec private findIndexofAEleFromAList (list:string list) (name:string) =
    match list with 
    | [] -> raise <| AnalysisException $"Could not find the corresponding index from the system for %s{name}"
    | hd :: tail -> if hd = name then 0 else 1+ findIndexofAEleFromAList tail name

let rec private findCurrentTrace (mappings:list<(String * int * int * int)>)  (index:int) =
    match mappings with 
    | [] -> []
    | (xl, xs, ap_nba_index, ap_sys_Index) :: tail -> 
        if index = xs then (xl, ap_nba_index, ap_sys_Index) :: findCurrentTrace tail index
        else findCurrentTrace tail index

let rec findValueFromAListByPosition (conjunctions:list<Literal<int>>) (position:int)  = 
    match conjunctions with 
    | [] -> raise <| AnalysisException $"error dnfWithConstrains"
    | hd :: tail -> 
        if position = 0 then hd 
        else findValueFromAListByPosition tail (position-1)

let findValueFromAListByPositions (conjunctions:list<Literal<int>>) (positions:int list)  = 
    List.map 
        (fun hd -> 
            findValueFromAListByPosition conjunctions hd
    ) positions

let private dnfWithConstrains (dnf:DNF<int>) (sys_positions_valuations:list<int * bool>) = 
    let rec checkIfAllPairAreTheSame (li1:list<bool>) (li2:list<Literal<int>>) : bool = 
        match (li1, li2) with 
        | ([], []) -> true 
        | ((hd1::tail1), (hd2::tail2)) ->
            (match (hd1, hd2) with 
            | (true, PL _ ) -> checkIfAllPairAreTheSame tail1 tail2
            | (false, NL _ ) -> checkIfAllPairAreTheSame tail1 tail2
            | (_, _) -> false 
            )
        | _ -> false 


    dnf
    |> List.filter (fun conjunctions -> 
        let (positions:list<int>) = List.map (fun (a, b) -> a ) sys_positions_valuations
        let (valuations:list<bool>) = List.map (fun (a, b) -> b ) sys_positions_valuations
        let (value_at_position:list<Literal<int>>) = findValueFromAListByPositions conjunctions positions 
        checkIfAllPairAreTheSame valuations value_at_position
        )
 

let private generateNextStep 
    (sysStates:Set<int>) 
    (nbaStates:Set<int>) 
    ts 
    nba 
    (mappings:list<(String * int * int * int)>) 
    (traceIndex:int) = 
    let (secondSystemStates:Set<(Set<int> * Set<int>)>) = findNextStatesFromTransitionSystem ts sysStates
    let (secondNbaStates:Set<(DNF<int> * int) list>) = findNextStatesFromNBA nba nbaStates 

    let (product:list<(Set<int> * Set<int> * int * DNF<int>)>) = 
        secondSystemStates 
        |> Set.toList
        |> List.map (fun (sucs, apEval) -> 
            //let (listOfSecondNbaStates:list<DNF<int>*int>) = 
            secondNbaStates 
            |> Set.toList 
            |> List.map (fun li -> 
                li 
                |> List.map (fun (dnf, state) -> 
                    //printfn "sucs:  %s" (string_of_set_elements sucs)
                    //printfn "apEval:%s" (string_of_set_elements apEval)
                    //printfn "state :%d" (state)
                    //printfn "dnf   :%s" (DNF.print dnf)
                    let var_name_ap_system_pos = findCurrentTrace mappings (traceIndex)
                    //printfn "=====================" 
                    let (sys_positions:list<int>) = 
                        var_name_ap_system_pos 
                        |> List.map (fun (var_name, ap_nba_pos, ap_system_pos) -> 
                            //printfn "var_name :%s" (var_name)
                            //printfn "ap_nba_pos:%d" (ap_nba_pos)
                            //printfn "ap_system_pos:%d" (ap_system_pos)
                            ap_system_pos)
                    let (sys_positions_valuations:list<int * bool>) = 
                        sys_positions
                        |> List.map (fun sys_pos -> (sys_pos, Set.exists (fun i -> i = sys_pos) apEval)) 
                    let (dnf_after_aline_with_system:DNF<int>) = 
                        dnfWithConstrains dnf sys_positions_valuations

                    (dnf_after_aline_with_system, state)
                             
                    )
                )
            |> List.concat
            |> List.map (fun (dnf, state) -> (sucs, apEval, state, dnf))
            )
        |> List.concat

    
    //printfn "Length Product %d" (List.length product)
    product.Head 
    (* Here is wrong.... *)

let string_of_transition_system (ts : TransitionSystem<String>)  =
    let printing = TransitionSystem.print (fun a -> a) ts
    printfn$"\n(system_After_bisim: %s{printing})" 
        

let string_of_property_automata (nba : NBA<int, (String * int)>) = 
    let stateStringer = (fun a-> string a) 
    let alphStringer = (fun (a, i) -> a + "_" + string i)
    let s = new StringWriter() 
    s.WriteLine("HOA: v1")
    s.WriteLine ("States: " + string(nba.States.Count))
    for n in nba.InitialStates do 
        s.WriteLine ("Start: " + stateStringer(n))
    s.WriteLine ("AP: " + string(nba.APs.Length) + " " + List.fold (fun s x -> s + " \"" + alphStringer(x) + "\"") "" nba.APs)
    for n in nba.States do 
        let edges = nba.Edges.[n]
        let accString = 
            if nba.AcceptingStates.Contains n then 
                "{0}"
            else 
                ""
        s.WriteLine("State: " + stateStringer(n) + " " + accString)
        for (g, n') in edges do 
            s.WriteLine("[" + DNF.print g + "] " + stateStringer(n'))
    // let nbaprinting = NBA.toHoaString (fun a-> string a) (fun (a, i) -> a + "_" + string i) nba
    printfn$"\n(nba_printing: %s{s.ToString()})" 

(* sys_state, nba_state, dnf_label *)

let rec findAllTheCycles 
    (mappings:list<(String * int * int * int)>) (config : Configuration) 
    (ts : TransitionSystem<String>)  (nba : NBA<int, (String * int)>) 
    (sysStates:Set<int>)  (nbaStates:Set<int>) 
    (history: Record) (traceIndex:int) : list <Record * (int * int)> = 

    //printfn "findAllTheCycles: sys: %s, nba:%s" (string_of_set_elements sysStates) (string_of_set_elements nbaStates)


    let (nextSystemStates:Set<(Set<int> * Set<int>)>) = findNextStatesFromTransitionSystem ts sysStates
    let (systemTransitions:list<(int * int * Set<int>)>) = 
        (* list of tuples: (current state, next state, transition label) *)
        nextSystemStates 
        |> Set.toList 
        |> List.map (fun (successors, sys_label) -> 
            successors 
            |> Set.toList 
            |> List.map (fun successor -> 
                sysStates
                |> Set.toList 
                |> List.map (fun current -> (current, successor, sys_label))
                )
            |> List.concat    
            )
        |> List.concat 

    let (nextNbaStates:Set<(DNF<int> * int) list>) = findNextStatesFromNBA nba nbaStates 
    let (nbaTransitions:list<(int * int * DNF<int>)>) = 
        (* list of tuples: (current state, next state, transition label) *)
        nextNbaStates
        |> Set.toList 
        |> List.map 
            (fun li ->  
                li 
                |> List.map (fun (dnf, successor) -> 
                    nbaStates
                    |> Set.toList 
                    |> List.map (fun current -> (current, successor, dnf))
                    )
                |> List.concat
            )
        |> List.concat


    let rec iterateNBATrans (sysTran:(int * int * Set<int>)) (nbaTrans:list<(int * int * DNF<int>)>) : list<Record * (int * int)> = 
        let (sys_current, sys_next, sys_label) = sysTran
        match nbaTrans with 
        | [] -> [] 
        | hd::tail -> 
          let (nba_current, nba_next, nab_label) = hd
          let var_name_ap_system_pos = findCurrentTrace mappings (traceIndex)
          let (sys_positions:list<int>) = 
                        var_name_ap_system_pos 
                        |> List.map (fun (var_name, ap_nba_pos, ap_system_pos) -> 
                            //printfn "var_name :%s" (var_name)
                            //printfn "ap_nba_pos:%d" (ap_nba_pos)
                            //printfn "ap_system_pos:%d" (ap_system_pos)
                            ap_system_pos)
          let (sys_positions_valuations:list<int * bool>) = 
                        sys_positions
                        |> List.map (fun sys_pos -> (sys_pos, Set.exists (fun i -> i = sys_pos) sys_label)) 
          let (dnf_after_aline_with_system:DNF<int>) = dnfWithConstrains nab_label sys_positions_valuations

          let (history':Record) = history @ [(sys_current, nba_current, dnf_after_aline_with_system)]

          if recordReoccur history (sys_next, nba_next) then 
            //printfn "----- sys_next: %d, nba_next:%d ----- " sys_next nba_next
            [(history', (sys_next, nba_next))] 
          else findAllTheCycles mappings config ts nba (Set.ofList [sys_next]) (Set.ofList [nba_next]) history' traceIndex

    let rec iterateSysTrans (sysTrans:list<(int * int * Set<int>)>) (nbaTrans:list<(int * int * DNF<int>)>) : list<Record * (int * int)> = 
        match sysTrans with 
        | [] -> []
        | hd::tail -> iterateNBATrans hd nbaTrans @ iterateSysTrans tail nbaTrans


    iterateSysTrans systemTransitions nbaTransitions



let rec string_of_record (record:Record) = 
    record
    |> List.map (fun (a, b, dnf) ->  string a  ^ ","^ string b ^ ","^ DNF.print dnf)
    |> Util.combineStringsWithSeperator ";\n"

let rec string_of_records (records:list<Record * (int * int)>) = 
    records
    |> List.map (fun (a, (end_sys, end_nba))-> 
        string_of_record a ^ 
        "\nreoccurrence with " ^ 
        string end_sys ^ ", " ^ 
        string end_nba
        

        )
    |> Util.combineStringsWithSeperator "\n==================\n\n"



let rec private on_the_Fly_HyperLTL_MC 
    (quantifiers:list<TraceQuantifierType>)  (* current quantifiers list, and its head is the current quantifier *)
    (mappings:list<(String * int * int * int)>) (* mapping from var_name -> trance index -> nba_ap_index -> system_ap_index *)
    (config : Configuration) (* This is for printing *)
    (ts : TransitionSystem<String>) (* transition system *)
    (nba : NBA<int, (String * int)>) (* property automata *)
    (traceIndex:int) (* current trace index, for matching the valuations from teh system and property automata *)
    = 
    if quantifiers.Length = 2 then true (* for now *)
    else         
        
        string_of_transition_system ts 
        string_of_property_automata nba

        printfn "==========================" 

        let traces = findAllTheCycles mappings config ts nba (ts.InitialStates) (nba.InitialStates) [] traceIndex
        printfn "Traces :\n%s\n%d" (string_of_records traces) (List.length traces)

        let memorization = new Dictionary<int, (Set<int> * Set<int> * int * DNF<int>)>() 
        let (product: (Set<int> * Set<int> * int * DNF<int>) )  = generateNextStep (ts.InitialStates) (nba.InitialStates) ts nba mappings traceIndex

        // <system states, system transition label, nba states, nba transition DNF>
        memorization.Add (0, product ) 

        let mutable Index = 0 
        let mutable Break = false

        while not Break do
            let ((systemStates, _, nbaStates, _)) = memorization[Index]

            let (nextProduct: (Set<int> * Set<int> * int * DNF<int>) )  = generateNextStep (systemStates) (Set.empty.Add(nbaStates)) ts nba mappings traceIndex


            if existRecord memorization nextProduct then Break <- true
            else 
                Index <- Index + 1
                memorization.Add (Index, nextProduct) 


        (*
        let c = memorization.Count
        for pair in memorization do
            printfn "%A" pair
        *)

        on_the_Fly_HyperLTL_MC (quantifiers.Tail) mappings config ts nba (traceIndex+1) 


        (*match quantifiers.Head with 
        | EXISTS -> 
            printfn$"\n(Current quantifier: exists)"  
            (* TBD *)
            on_the_Fly_HyperLTL_MC (quantifiers.Tail) mappings config ts nba (traceIndex+1) 
        | FORALL -> 
            printfn$"\n(Current quantifier: forall)" 
            // <system states, system transition label, nba state, nba transition DNF>
        *)


let private verify_on_the_Fly 
    (config : Configuration) 
    (tslist : list<TransitionSystem<String>>) 
    (hyperltl : HyperLTL<String>) = 
    printfn$"\n===========================================================" 
    printfn$"=================== Start of SYH's Code ===================" 
    printfn$"===========================================================\n" 

    let swtotal = System.Diagnostics.Stopwatch()
    swtotal.Start()

    // print the system
    let system = tslist[0] 

    //let property = HyperLTL.print (fun a -> a) hyperltl
    //printfn$"\n(property: %s{property})" 

    let quantifiers = hyperltl.QuantifierPrefix 
    let (ltl :  LTL<'L * int>) = hyperltl.LTLMatrix

    // var_name, ap_label_nba, ap_nba_index, ap_label_system
    let (mappings : list<String*int*int*int> ) = 
        ltl 
        |> LTL.allAtoms
        |> Set.toList
        |> List.mapi 
            (fun i (xl, xs) -> 
                let ap_sys_Index = findIndexofAEleFromAList (system.APs) xl
                (xl, xs, i, ap_sys_Index))

    // mapping from var_trace -> labels, e.g., (mapping: l_0-1 ~~> l2 ~~> 2)
    // let (mappings : list<String*int*int> )  
    // var_name, ap_label_nba, ap_label_system
    mappings 
    |> List.map 
        (fun (xl, xs, ap_nba_index, ap_sys_Index) -> 
        let a = "l" + string ap_nba_index
        printfn$"\n(mapping= var: %s{xl}-ap_nba:%d{xs} ~~> %s{a} ~~~ ap_system:%d{ap_sys_Index})")

    // get the property's NBA
    let (nba  : NBA<int, (String * int)>) = 
        match FsOmegaLib.Operations.LTLConversion.convertLTLtoNBA Util.DEBUG config.SolverConfig.MainPath config.SolverConfig.Ltl2tgbaPath.Value ltl with 
        | Success aut -> aut 
        | Fail err -> 
            config.LoggerN err.DebugInfo
            raise <| AnalysisException err.Info

    // starts with the first trace variable, indexed with 0
    let res = on_the_Fly_HyperLTL_MC quantifiers mappings config system nba 0 

    if res then 
        printfn "\nSAT (on_the_Fly_HyperLTL_MC)\n"
    else
        printfn "\nUNSAT (on_the_Fly_HyperLTL_MC)\n"

    swtotal.Stop()
    config.LoggerN $"End of SYH code time: %i{swtotal.ElapsedMilliseconds}ms (~=%.2f{double(swtotal.ElapsedMilliseconds) / 1000.0}s)"
    printfn$"\n========================================================" 
    printfn$"================== End of SYH's Code ===================" 
    printfn$"========================================================\n" 



let private verify config (tslist : list<TransitionSystem<String>>) (hyperltl : HyperLTL<String>) (m : Mode) = 
    let res, t = ModelChecking.modelCheck config tslist hyperltl m

    config.LoggerN ""

    if res then 
        printfn "SAT"
    else
        printfn "UNSAT"

    // Add a fresh line
    config.LoggerN ""
    
    config.LoggerN $"Model-checking time: %i{t.TotalTime}ms (~=%.2f{double(t.TotalTime) / 1000.0}s)"

    verify_on_the_Fly config tslist hyperltl 

let explictSystemVerification (config : Configuration) systemPaths propPath m  = 
    let sw: System.Diagnostics.Stopwatch = System.Diagnostics.Stopwatch()
    sw.Start()

    let hyperltlcontent =   
        try 
            File.ReadAllText propPath
        with 
        | _ -> raise <| AnalysisException $"Could not open/read file %s{propPath}"
                
    let tscontent = 
        systemPaths
        |> List.map (fun x -> 
            try 
                File.ReadAllText  x
            with 
            | _ -> raise <| AnalysisException $"Could not open/read file %s{x}"
        )

    config.LoggerN $"Read input (%i{sw.ElapsedMilliseconds}ms)"

    sw.Restart()


    let hyperltl =
        match HyperLTL.Parser.parseNamedHyperLTL Util.ParserUtil.escapedStringParser hyperltlcontent with 
        | Result.Ok x ->
            NamedHyperLTL.toHyperLTL x
        | Result.Error err -> 
            raise <| AnalysisException $"The HyperLTL formula could not be parsed: %s{err}"
                
                
    if HyperLTL.isConsistent hyperltl |> not then
        raise <| AnalysisException "HyperLTL formula is not consistent" 

    let tsList = 
        tscontent
        |> List.map (fun x -> 
            match TransitionSystemLib.TransitionSystem.Parser.parseTransitionSystem x with 
                | Result.Ok y -> y 
                | Result.Error msg -> 
                    raise <| AnalysisException $"The explicit-state system could not be parsed: %s{msg}"
        )

    config.LoggerN $"Parsed input (%i{sw.ElapsedMilliseconds}ms)"

    // Check the systems 
    tsList
    |> List.iteri (fun i ts ->
        match TransitionSystem.findError ts with 
        | None -> ()
        | Some msg -> 
            raise <| AnalysisException $"Found error in the %i{i}th system: %s{msg}"
        )

    config.LoggerN $"System sizes: %A{tsList |> List.map (fun ts -> ts.States.Count)}"

    let tsList = 
        if config.ModelCheckingOptions.ComputeBisimulation then     
            // Compute bisimulation quotient
            sw.Restart()
            let bisim = 
                tsList
                |> List.map (fun ts -> TransitionSystem.computeBisimulationQuotient ts |> fst)

            config.LoggerN $"Computed bisimulation quotient (%i{sw.ElapsedMilliseconds}ms)"
            config.LoggerN $"System sizes: %A{tsList |> List.map (fun ts -> ts.States.Count)}"

            bisim        
        else 
            tsList
    
    let tsList =
        if tsList.Length > 1 then 
            if tsList.Length <> hyperltl.QuantifierPrefix.Length then 
                raise <| AnalysisException "The number of systems given does not match the property"
            tsList
        else  
            List.init (hyperltl.QuantifierPrefix.Length) (fun _ -> tsList.[0])
    
    hyperltl.LTLMatrix
    |> FsOmegaLib.LTL.LTL.allAtoms
    |> Set.iter (fun (x, i) ->
            if List.contains x tsList.[i].APs |> not then
                raise <| AnalysisException $"AP (%s{x}, %i{i}) is used in the HyperLTL formula, but AP %s{x} is not defined in the %i{i}th system"
            )
            
    verify config tsList hyperltl m

let nuSMVSystemVerification (config: Configuration) systemPaths propPath m  = 
    let sw: System.Diagnostics.Stopwatch = System.Diagnostics.Stopwatch()
    sw.Start()

    let propContent = 
        try 
            File.ReadAllText propPath
        with 
            | _ -> 
                raise <| AnalysisException $"Could not open/read file %s{propPath}"

    let systemContents = 
        systemPaths 
        |> List.map (fun x -> 
            try 
                File.ReadAllText  x
            with 
                | _ -> 
                    raise <| AnalysisException $"Could not open/read file %s{x}"
            )

    config.LoggerN $"Read input (%i{sw.ElapsedMilliseconds}ms)"

    sw.Restart()

    let plist = 
        systemContents
        |> List.mapi (fun i s -> 
            match TransitionSystemLib.SymbolicSystem.Parser.parseSymbolicSystem s with 
            | Result.Ok x -> x 
            | Result.Error msg -> 
                raise <| AnalysisException $"The %i{i}th NuSMV system could not be parsed: %s{msg}"
        )

    let symbolicHyperLTL = 
        match HyperLTL.Parser.parseNamedSymbolicHyperltl propContent with
        | Result.Ok x ->
            HyperLTL.SymbolicHyperLTL.NamedSymbolicHyperLTL.toSymbolicHyperLTL x
        | Result.Error err -> 
            raise <| AnalysisException $"The HyperLTL formula could not be parsed. %s{err}"

    config.LoggerN $"Parsed input (%i{sw.ElapsedMilliseconds}m)s"

    // Check for error in the NuSMV models
    plist 
    |> List.iteri (fun i x -> 
        match SymbolicSystem.findError x with 
        | None -> ()
        | Some msg -> 
            raise <| AnalysisException $"Found error in the %i{i}th system: %s{msg}"
        )

    let unfoldRelationPredicate (a : RelationalAtom)  = 
        match a with 
        | UnaryPred (e, n) -> 
            LTL.Atom ((e, n))
        | RelationalEq(e1, n1, e2, n2) -> 
            let t1 = e1 |> TransitionSystemLib.SymbolicSystem.Expression.inferType (fun x -> if plist.Length = 1 then plist.[0].VarTypes |> Map.ofList |> Map.find x else plist.[n1].VarTypes |> Map.ofList |> Map.find x)
            let t2 = e2 |> TransitionSystemLib.SymbolicSystem.Expression.inferType (fun x -> if plist.Length = 1 then plist.[0].VarTypes |> Map.ofList |> Map.find x else plist.[n2].VarTypes |> Map.ofList |> Map.find x)

            let t = 
                match TransitionSystemLib.SymbolicSystem.VariableType.joinTypes t1 t2 with 
                | Some x -> x 
                | None -> 
                    raise <| AnalysisException $"Error during unfolding: Could not unify types %A{t1} and %A{t1}."

            VariableType.allValues t
            |> List.map (fun v -> 
                LTL.And(
                    LTL.Atom((Expression.Eq(e1, v |> VariableValue.toConstant |> Expression.Const), n1)),
                    LTL.Atom((Expression.Eq(e2, v |> VariableValue.toConstant |> Expression.Const), n2))
                )
            )
            |> List.reduce (fun x y -> LTL.Or(x, y))

    let unfoldedHyperLTL = 
        {
            HyperLTL.QuantifierPrefix = symbolicHyperLTL.QuantifierPrefix
            HyperLTL.LTLMatrix = symbolicHyperLTL.LTLMatrix |> LTL.bind (fun x -> unfoldRelationPredicate x)
        }
        
    if HyperLTL.isConsistent unfoldedHyperLTL |> not then
        raise <| AnalysisException "HyperLTL formula is not consistent"

    sw.Restart()
    
    let tsList = 
        if plist.Length = 1 then 
            let atomList = 
                unfoldedHyperLTL.LTLMatrix
                |> LTL.allAtoms
                |> Set.map fst 
                |> Set.toList
                
            atomList
            |> List.iter (fun (v : Expression) ->
                v 
                |> Expression.allVars
                |> Set.iter (fun x ->
                    if (Map.containsKey x plist.[0].VarTypeMap |> not) && (plist.[0].DefineMap.Keys.Contains x |> not) then
                        raise <| AnalysisException $"Variable %A{x} is used in an atomic proposition but not defined in the system"
                    )
            )
              
            let ts = 
                SymbolicSystem.convertSymbolicSystemToTransitionSystem plist.[0] atomList

            List.init (unfoldedHyperLTL.QuantifierPrefix.Length) (fun _ -> ts)
        else 
            if plist.Length <> unfoldedHyperLTL.QuantifierPrefix.Length then 
                raise <| AnalysisException "The number of systems given does not match the property"

            [0..unfoldedHyperLTL.QuantifierPrefix.Length-1]
            |> List.map (fun i -> 
                let atomList = 
                    unfoldedHyperLTL.LTLMatrix
                    |> LTL.allAtoms
                    |> Set.filter (fun (_, j) -> i = j) // Only those atoms that are rlevent
                    |> Set.map fst 
                    |> Set.toList
                    
                atomList
                |> List.iter (fun (v : Expression) ->
                    v
                    |> Expression.allVars
                    |> Set.iter (fun x ->
                            if plist.[i].VarTypeMap.ContainsKey x |> not && (plist.[i].DefineMap.ContainsKey x |> not) then
                                raise <| AnalysisException $"Variable %A{x} is used in an atomic proposition but defined in the %i{i}th system"
                        )
                )
                    
                SymbolicSystem.convertSymbolicSystemToTransitionSystem plist.[i] atomList
                )
                 
    config.LoggerN $"Compiled programs to explicit-state TSs (%i{sw.ElapsedMilliseconds}ms)"
    config.LoggerN $"System sizes: %A{tsList |> List.map (fun ts -> ts.States.Count)}"


    sw.Restart()
    let tsList = 
        if config.ModelCheckingOptions.ComputeBisimulation then     
            // Compute bisimulation quotient
            sw.Restart()
            let bisim = 
                tsList
                |> List.map (fun ts -> TransitionSystem.computeBisimulationQuotient ts |> fst)

            config.LoggerN $"Computed bisimulation quotient (%i{sw.ElapsedMilliseconds}ms)"
            config.LoggerN $"System sizes: %A{bisim |> List.map (fun ts -> ts.States.Count)}"

            bisim        
        else 
            tsList

    // Convert the APs in the system to be strings
    let tsList = 
        tsList 
        |> List.map (fun ts -> TransitionSystem.mapAPs (fun (x: Expression) -> Expression.print x) ts)
    

    let hyperltl = 
        {
            HyperLTL.QuantifierPrefix = unfoldedHyperLTL.QuantifierPrefix
            LTLMatrix = LTL.map (fun (x: Expression, n) -> (Expression.print x, n)) unfoldedHyperLTL.LTLMatrix
        }

    verify config tsList hyperltl m


let booleanProgramVerification (config: Configuration) systemPaths propPath m  = 
    let sw = System.Diagnostics.Stopwatch()
    let totalsw = System.Diagnostics.Stopwatch()
    totalsw.Start()
    sw.Start()

    let hyperltlcontent =
        try 
            File.ReadAllText propPath
        with 
            | _ -> 
                raise <| AnalysisException $"Could not open/read file %s{propPath}"
               
    let progcontents = 
        systemPaths
        |> List.map (fun x -> 
            try 
                File.ReadAllText  x
            with 
                | _ -> 
                    raise <| AnalysisException $"Could not open/read file %s{x}"
            )

    config.LoggerN $"Read input (%i{sw.ElapsedMilliseconds}ms)"

    sw.Restart()

    let hyperltl = 
        match HyperLTL.Parser.parseBooleanProgramNamedHyperLTL hyperltlcontent with
        | Result.Ok x ->
            NamedHyperLTL.toHyperLTL x
        | Result.Error err -> 
            raise <| AnalysisException $"The provided HyperLTL formula could not be parsed: %s{err}"

    if HyperLTL.isConsistent hyperltl |> not then
        raise <| AnalysisException "HyperLTL formula is not consistent"

    let progList = 
        progcontents
        |> List.mapi (fun i s -> 
            match TransitionSystemLib.BooleanProgramSystem.Parser.parseBooleanProgram s with 
                | Ok x -> x
                | Error msg -> 
                    raise <| AnalysisException $"The %i{i}th boolean program could not be parsed: %s{msg}"
            )

    config.LoggerN $"Parsed input (%i{sw.ElapsedMilliseconds}ms)"

    progList
    |> List.iteri (fun i x -> 
        match BooleanProgram.findError x with 
        | None -> ()
        | Some msg -> 
            raise <| AnalysisException $"Found error in the %i{i}th system: %s{msg}"
        )

    sw.Restart()

    let tsList = 
        if progList.Length = 1 then 
            // Use the same system for all traces
            let prog = progList[0]

            let relevantAps = 
                hyperltl.LTLMatrix
                |> LTL.allAtoms
                |> Set.map (fun (x, _) -> x)
                |> Set.toList
                
            relevantAps
            |> List.iter (fun (v, i) ->
                printfn$"\n(relevantAps: %s{v}-%d{i})" 
                if prog.DomainMap.ContainsKey v && prog.DomainMap.[v] > i |> not then
                    raise <| AnalysisException $"AP (%A{v}, %i{i}) is used in the HyperLTL property but variable %A{v} does not exists or has not the required bit width"
                )

            let ts = 
                BooleanProgram.convertBooleanProgramToTransitionSystem prog relevantAps
                |> TransitionSystem.mapAPs (fun (n, i) -> 
                    n + "_" + string(i))

        
            let temp = TransitionSystem.print (fun a -> a) ts
            printfn$"\n(TransitionSystem: %s{temp})" 



            config.LoggerN $"Compiled Program to explicit-state TS (%i{sw.ElapsedMilliseconds}ms)"

            // PRINT ts

            List.init (hyperltl.QuantifierPrefix.Length) (fun _ -> ts)
        else 
            // Different system for all traces 
            if progList.Length <> hyperltl.QuantifierPrefix.Length then 
                raise <| AnalysisException "The number of systems given does not match the property"

            [0..hyperltl.QuantifierPrefix.Length-1]
            |> List.map (fun i ->   
                let relevantAps = 
                    hyperltl.LTLMatrix
                    |> LTL.allAtoms
                    |> Set.filter (fun (_, j) ->  i = j) // Only those atom used in this copy
                    |> Set.map (fun (x, _) -> x)
                    |> Set.toList
                    
                    
                relevantAps
                |> List.iter (fun (v, j) ->
                    if progList.[i].DomainMap.ContainsKey v && progList.[i].DomainMap.[v] > j |> not then
                        raise <| AnalysisException $"AP (%A{v}, %i{j}) is used in the HyperLTL property but variable %A{v} does not exists or has not the required bit width. Aborting."
                    )
                BooleanProgram.convertBooleanProgramToTransitionSystem progList.[i] relevantAps
                |> TransitionSystem.mapAPs (fun (n, i) -> n + "_" + string(i))
            )

    config.LoggerN $"Compiled Program to explicit-state TS (%i{sw.ElapsedMilliseconds}ms)"
    config.LoggerN $"System sizes: %A{tsList |> List.map (fun ts -> ts.States.Count)}"


    sw.Restart()
    let tsList = 
        if config.ModelCheckingOptions.ComputeBisimulation then     
            // Compute bisimulation quotient
            sw.Restart()
            let bisim = 
                tsList
                |> List.map (fun ts -> TransitionSystem.computeBisimulationQuotient ts |> fst)

            config.LoggerN $"Computed bisimulation quotient (%i{sw.ElapsedMilliseconds}ms)"
            config.LoggerN $"System sizes: %A{bisim |> List.map (fun ts -> ts.States.Count)}"

            bisim        
        else 
            tsList

    let hyperltl = 
        {
            HyperLTL.QuantifierPrefix = hyperltl.QuantifierPrefix
            HyperLTL.LTLMatrix = hyperltl.LTLMatrix |> LTL.map (fun ((n, i), j) -> n + "_" + string(i), j)
        }

    verify config tsList hyperltl m
