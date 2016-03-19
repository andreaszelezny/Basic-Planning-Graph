// Contains all preconditions for all possible actions
let allPreconds =
    Map.empty.
        Add("Mr12", Set.ofList ["r1"]).
        Add("Mr21", Set.ofList ["r2"]).
        Add("Mq12", Set.ofList ["q1"]).
        Add("Mq21", Set.ofList ["q2"]).
        Add("Lar1", Set.ofList ["a1";"r1";"ur"]).
        Add("Lar2", Set.ofList ["a2";"r2";"ur"]).
        Add("Laq1", Set.ofList ["a1";"q1";"uq"]).
        Add("Laq2", Set.ofList ["a2";"q2";"uq"]).
        Add("Lbr1", Set.ofList ["b1";"r1";"ur"]).
        Add("Lbr2", Set.ofList ["b2";"r2";"ur"]).
        Add("Lbq1", Set.ofList ["b1";"q1";"uq"]).
        Add("Lbq2", Set.ofList ["b2";"q2";"uq"]).
        Add("Uar1", Set.ofList ["ar";"r1"]).
        Add("Uar2", Set.ofList ["ar";"r2"]).
        Add("Uaq1", Set.ofList ["aq";"q1"]).
        Add("Uaq2", Set.ofList ["aq";"q2"]).
        Add("Ubr1", Set.ofList ["br";"r1"]).
        Add("Ubr2", Set.ofList ["br";"r2"]).
        Add("Ubq1", Set.ofList ["bq";"q1"]).
        Add("Ubq2", Set.ofList ["bq";"q2"])

// Contains all positive effects of all actions
let allPEffects =
    Map.empty.
        Add("Mr12", Set.ofList ["r2"]).
        Add("Mr21", Set.ofList ["r1"]).
        Add("Mq12", Set.ofList ["q2"]).
        Add("Mq21", Set.ofList ["q1"]).
        Add("Lar1", Set.ofList ["ar"]).
        Add("Lar2", Set.ofList ["ar"]).
        Add("Laq1", Set.ofList ["aq"]).
        Add("Laq2", Set.ofList ["aq"]).
        Add("Lbr1", Set.ofList ["br"]).
        Add("Lbr2", Set.ofList ["br"]).
        Add("Lbq1", Set.ofList ["bq"]).
        Add("Lbq2", Set.ofList ["bq"]).
        Add("Uar1", Set.ofList ["a1";"ur"]).
        Add("Uar2", Set.ofList ["a2";"ur"]).
        Add("Uaq1", Set.ofList ["a1";"uq"]).
        Add("Uaq2", Set.ofList ["a2";"uq"]).
        Add("Ubr1", Set.ofList ["b1";"ur"]).
        Add("Ubr2", Set.ofList ["b2";"ur"]).
        Add("Ubq1", Set.ofList ["b1";"uq"]).
        Add("Ubq2", Set.ofList ["b2";"uq"])

// Contains all negative effects of all actions
let allNEffects =
    Map.empty.
        Add("Mr12", Set.ofList ["r1"]).
        Add("Mr21", Set.ofList ["r2"]).
        Add("Mq12", Set.ofList ["q1"]).
        Add("Mq21", Set.ofList ["q2"]).
        Add("Lar1", Set.ofList ["a1";"ur"]).
        Add("Lar2", Set.ofList ["a2";"ur"]).
        Add("Laq1", Set.ofList ["a1";"uq"]).
        Add("Laq2", Set.ofList ["a2";"uq"]).
        Add("Lbr1", Set.ofList ["b1";"ur"]).
        Add("Lbr2", Set.ofList ["b2";"ur"]).
        Add("Lbq1", Set.ofList ["b1";"uq"]).
        Add("Lbq2", Set.ofList ["b2";"uq"]).
        Add("Uar1", Set.ofList ["ar"]).
        Add("Uar2", Set.ofList ["ar"]).
        Add("Uaq1", Set.ofList ["aq"]).
        Add("Uaq2", Set.ofList ["aq"]).
        Add("Ubr1", Set.ofList ["br"]).
        Add("Ubr2", Set.ofList ["br"]).
        Add("Ubq1", Set.ofList ["bq"]).
        Add("Ubq2", Set.ofList ["bq"])

let allActions = allPreconds |> Map.toList |> List.map fst |> Set.ofList        // All possible actions

let initState = Set.ofList ["r1"; "q2"; "a1"; "b2"; "ur"; "uq"]         // Initial state of the problem

let endState = Set.ofList ["a2"; "b1"]         // Goal state that needs to be reached

// Basic Planning Graph (no mutex)
// maxK: Maximum number of iterations (needed for array sizing)
// zeroState: Initial state of problem
// goalState: Goal state that needs to be reached
type Graph(maxK:int, zeroState:Set<string>, goalState: Set<string>) = class
    let mutable k = 0
    let propLayers = Array.zeroCreate<Set<string>> (maxK+1)    // array of proposition layers
    let actionLayers = Array.zeroCreate<Set<string>> (maxK+1)  // array of action layers
    let pre = Array.zeroCreate<Set<string*string>> (maxK+1)    // array of preconditons
    let epos = Array.zeroCreate<Set<string*string>> (maxK+1)   // array of positive effects
    let eneg = Array.zeroCreate<Set<string*string>> (maxK+1)   // array of negative effects

    do propLayers.[0] <- zeroState      // Initialization with start state

    member x.ActionLayers = actionLayers
    member x.PropositionLayers = propLayers
    member x.Preconditions = pre
    member x.PostiveEffects = epos
    member x.NegativeEffects = eneg
    member x.ContainsGoal = Set.isSubset goalState propLayers.[k]       // Has the goal state already been reached in this iteration?
    member x.Expand() = 
        if k < maxK then
            k <- k + 1
            actionLayers.[k] <- Set.filter (fun a -> Set.isSubset allPreconds.[a] propLayers.[k-1]) allActions
            propLayers.[k] <- Set.union propLayers.[k-1] (Set.fold (fun pset a -> Set.union pset allPEffects.[a]) Set.empty actionLayers.[k])
            pre.[k] <- Set.fold (fun pre a -> 
                let pset = Set.intersect propLayers.[k-1] allPreconds.[a]
                let pset2 = pset |> Set.map (fun p -> (p,a))
                Set.union pre pset2) Set.empty actionLayers.[k]
            epos.[k] <- Set.fold (fun pe a -> 
                let pset = Set.intersect propLayers.[k] allPEffects.[a]
                let pset2 = pset |> Set.map (fun p -> (a,p))
                Set.union pe pset2) Set.empty actionLayers.[k]
            eneg.[k] <- Set.fold (fun ne a -> 
                let pset = Set.intersect propLayers.[k] allNEffects.[a]
                let pset2 = pset |> Set.map (fun p -> (a,p))
                Set.union ne pset2) Set.empty actionLayers.[k]
end

let g = new Graph(10,initState,endState)
g.Expand()
g
