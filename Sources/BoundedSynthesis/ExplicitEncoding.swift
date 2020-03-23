import Utils
import CAiger
import Logic
import Automata
import Specification
import TransitionSystem

enum NodeType: Int, CustomStringConvertible {
    case TERMINAL = 0, AND, OR, NOT, NONE

    var description: String {
        "\(self.rawValue)"
    }
}

struct ExplicitEncoding: BoSyEncoding {

    let options: BoSyOptions
    let automaton: CoBüchiAutomaton
    let specification: SynthesisSpecification

    // intermediate results
    var assignments: BooleanAssignment?
    var solutionBound: Int

    init(options: BoSyOptions, automaton: CoBüchiAutomaton, specification: SynthesisSpecification) {
        self.options = options
        self.automaton = automaton
        self.specification = specification

        assignments = nil
        solutionBound = 0
    }

    func getEncoding(forBound bound: Int) -> Logic? {
        let P = 3 // TODO add P as bound of tree size

        let states = 0..<bound

        let inputPropositions: [Proposition] = specification.inputs.map({ Proposition($0) })

        // assignment that represents initial state condition
        var initialAssignment: BooleanAssignment = [:]
        for state in automaton.initialStates {
            initialAssignment[lambda(0, state)] = Literal.True
        }

        var matrix: [Logic] = []
        //matrix.append(automaton.initialStates.reduce(Literal.True, { (val, state) in val & lambda(0, state) }))

        for source in states {
            // for every valuation of inputs, there must be at least one tau enabled
            var conjunction: [Logic] = []
            for i in allBooleanAssignments(variables: inputPropositions) {
                let disjunction = states.map({ target in tau(source, i, target) })
                        .reduce(Literal.False, |)
                conjunction.append(disjunction)
            }
            matrix.append(conjunction.reduce(Literal.True, &))

            func getRenamer(i: BooleanAssignment) -> RenamingBooleanVisitor {
                if specification.semantics == .mealy {
                    return RenamingBooleanVisitor(rename: { name in self.specification.outputs.contains(name) ? self.output(name, forState: source, andInputs: i) : name })
                } else {
                    return RenamingBooleanVisitor(rename: { name in self.specification.outputs.contains(name) ? self.output(name, forState: source) : name })
                }
            }

            for q in automaton.states {
                var conjunct: [Logic] = []

                if let condition = automaton.safetyConditions[q] {
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        let evaluatedCondition = condition.eval(assignment: i)
                        let renamer = getRenamer(i: i)
                        conjunct.append(evaluatedCondition.accept(visitor: renamer))
                    }
                }

                guard let outgoing = automaton.transitions[q] else {
                    assert(conjunct.isEmpty)
                    continue
                }

                for (qPrime, guardCondition) in outgoing {
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        let evaluatedCondition = guardCondition.eval(assignment: i)
                        let transitionCondition = requireTransition(from: source, q: q, i: i, qPrime: qPrime, bound: bound, rejectingStates: automaton.rejectingStates)
                        if evaluatedCondition as? Literal != nil && evaluatedCondition as! Literal == Literal.True {
                            conjunct.append(transitionCondition)
                        } else {
                            let renamer = getRenamer(i: i)
                            conjunct.append(evaluatedCondition.accept(visitor: renamer) --> transitionCondition)
                        }
                    }
                }
                matrix.append(lambda(source, q) --> conjunct.reduce(Literal.True, &))
            }
        }

        //
        //
        //

        // (nodeType_q_k_p = TERMINAL) <-> (nodeAssignment_q_k_p != 0)
        // (nodeType_q_k_p = TERMINAL) <-> OR_x(nodeAssignment_q_k_p = x)
        for q in states {
            for k in states {
                for p in 1...P {
                    matrix.append(
                            nodeType(q, k, p, NodeType.TERMINAL) <->
                                    inputPropositions
                                            .map({ x in nodeAssignment(q, k, p, x) })
                                            .reduce(Literal.False, |)
                    )
                }
            }
        }

        // (nodeChild_q_k_p = ch) -> (nodeParent_q_k_ch = p)
        for q in states {
            for k in states {
                for p in 1...P {
                    for ch in 1...P {
                        matrix.append(nodeChild(q, k, p, ch) --> nodeParent(q, k, ch, p))
                    }
                }
            }
        }

        // (nodeParent_q_k_p != 0) <-> (nodeType_q_k_p != NONE) ; p != 1 (root)
        // OR_par(nodeParent_q_k_p == par) <-> !(nodeType_q_k_p = NONE)
        for q in states {
            for k in states {
                for p in 1...P {
                    if p != 1 {
                        matrix.append(
                                (1...P).map({ par in nodeParent(q, k, p, par) }).reduce(Literal.False, |)
                                        <-> (!nodeType(q, k, p, NodeType.NONE))
                        )
                    }
                }
            }
        }

        // (nodeType_q_k_p = AND | nodeType_q_k_p = OR) & (nodeChild_q_k_p = c) -> (nodeParent_q_k_c+1 = p)
        for q in states {
            for k in states {
                for p in 1...P {
                    for c in 1..<P {
                        matrix.append(
                                ((nodeType(q, k, p, NodeType.AND) | nodeType(q, k, p, NodeType.OR)) & nodeChild(q, k, p, c)) -->
                                        nodeParent(q, k, c + 1, p)
                        )
                    }
                }
            }
        }

        // alias between nodeValue(q, k, p=1, u) <-> tau(q, k, u)
        for c in states {
            for k in states {
                for i in allBooleanAssignments(variables: inputPropositions) {
                    matrix.append(nodeValue(c, k, 1, i) <-> tau(c, i, k))
                }
            }
        }

        // (nodeType_q_k_p = TERMINAL) & (nodeAssignment_q_k_p = x) -> AND_u(nodeValue_q_k_p_u <-> u_x)
        for q in states {
            for k in states {
                for p in 1...P {
                    for x in inputPropositions {
                        matrix.append(
                                (nodeType(q, k, p, NodeType.TERMINAL) & nodeAssignment(q, k, p, x)) -->
                                        allBooleanAssignments(variables: inputPropositions)
                                                .map({ u in nodeValue(q, k, p, u) <-> (u[x] ?? Literal.False) })
                                                .reduce(Literal.True, &)
                        )
                    }
                }
            }
        }

        // (nodeType_q_k_p = AND) & (nodeChild_q_k_p = c) -> AND_u(nodeValue_q_k_p_u <-> (nodeValue_q_k_c_u & nodeValue_q_k_c+1_u))
        for q in states {
            for k in states {
                for p in 1...P {
                    for c in 1..<P {
                        matrix.append(
                                (nodeType(q, k, p, NodeType.AND) & nodeChild(q, k, p, c)) -->
                                        allBooleanAssignments(variables: inputPropositions)
                                                .map({ u in nodeValue(q, k, p, u) <-> (nodeValue(q, k, c, u) & nodeValue(q, k, c + 1, u)) })
                                                .reduce(Literal.True, &)
                        )
                    }
                }
            }
        }

        // (nodeType_q_k_p = OR) & (nodeChild_q_k_p = c) -> AND_u(nodeValue_q_k_p_u <-> (nodeValue_q_k_c_u | nodeValue_q_k_c+1_u))
        for q in states {
            for k in states {
                for p in 1...P {
                    for c in 1..<P {
                        matrix.append(
                                (nodeType(q, k, p, NodeType.OR) & nodeChild(q, k, p, c)) -->
                                        allBooleanAssignments(variables: inputPropositions)
                                                .map({ u in nodeValue(q, k, p, u) <-> (nodeValue(q, k, c, u) | nodeValue(q, k, c + 1, u)) })
                                                .reduce(Literal.True, &)
                        )
                    }
                }
            }
        }

        // (nodeType_q_k_p = NOT) & (nodeChild_q_k_p = c) -> AND_u(nodeValue_q_k_p_u <-> !nodeValue_q_k_c_u)
        for q in states {
            for k in states {
                for p in 1...P {
                    for c in 1...P {
                        matrix.append(
                                (nodeType(q, k, p, NodeType.NOT) & nodeChild(q, k, p, c)) -->
                                        allBooleanAssignments(variables: inputPropositions)
                                                .map({ u in nodeValue(q, k, p, u) <-> !nodeValue(q, k, c, u) })
                                                .reduce(Literal.True, &)
                        )
                    }
                }
            }
        }

        // (nodeType_q_k_p = NONE) -> AND_u(!nodeValue_q_k_p_u)
        for q in states {
            for k in states {
                for p in 1...P {
                    matrix.append(
                            nodeType(q, k, p, NodeType.NONE) -->
                                    allBooleanAssignments(variables: inputPropositions)
                                            .map({ u in !nodeValue(q, k, p, u) })
                                            .reduce(Literal.True, &)
                    )
                }
            }
        }

        //
        //
        //

        for q in states {
            for k in states {
                for p in 1...P {
                    matrix.append(exactlyOne([
                        nodeType(q, k, p, NodeType.TERMINAL),
                        nodeType(q, k, p, NodeType.NONE),
                        nodeType(q, k, p, NodeType.AND),
                        nodeType(q, k, p, NodeType.NOT),
                        nodeType(q, k, p, NodeType.OR)
                    ]))
                }
            }
        }

        //
        //
        //

        // None-typed nodes have largest indices
        // (nodeType[p] = NONE) => (nodeType[p+1] = NONE)
        for q in states {
            for k in states {
                for p in 1..<P {
                    matrix.append(
                            nodeType(q, k, p, NodeType.NONE) --> nodeType(q, k, p + 1, NodeType.NONE)
                    )
                }
            }
        }

        // TODO
        // Only null-transitions have no guard (root is none-typed)
        // (transitionDestination = 0) <=> (nodeType[1] = NONE)
        // for (c in 1..C)
        //        for (k in 1..K)
        //            iff(
        //                transitionDestination[c, k] eq 0,
        //                nodeType[c, k, 1] eq NodeType.NONE
        //            )

        // child=>parent relation
        // (nodeChild[p] = ch) => (nodeParent[ch] = p)
        // Done upper
        // (nodeChild[p] = 0) => AND_{ch}(nodeParent[ch] != p)
        for q in states {
            for k in states {
                for p in 1...P {
                    matrix.append(
                            nodeChild(q, k, p, 0) --> (1...P).map({ ch in !nodeParent(q, k, ch, p) }).reduce(Literal.True, &)
                    )
                }
            }
        }

        // Only typed nodes, except the root, have parent
        for c in states {
            for k in states {
                for p in 2...P {
                    matrix.append(
                            (!nodeParent(c, k, p, 0)) <-> (!nodeType(c, k, p, NodeType.NONE))
                    )
                }
            }
        }

        // TERMINALS CONSTRAINTS

        // Only terminal nodes have associated input variables
        // (nodeType[p] = TERMINAL) <=> (nodeInputVariable[p] != 0)
        // Done upper

        // Terminals do not have children
        for c in states {
            for k in states {
                for p in 1...P {
                    matrix.append(
                            nodeType(c, k, p, NodeType.TERMINAL) --> nodeChild(c, k, p, 0)
                    )
                }
            }
        }

        // AND/OR NODES CONSTRAINTS

        // AND/OR nodes cannot have numbers P-1 or P
        for c in states {
            for k in states {
                if (P >= 1) {
                    matrix.append(!nodeType(c, k, P, NodeType.AND))
                    matrix.append(!nodeType(c, k, P, NodeType.OR))
                }
                if (P >= 2) {
                    matrix.append(!nodeType(c, k, P - 1, NodeType.AND))
                    matrix.append(!nodeType(c, k, P - 1, NodeType.OR))
                }
            }
        }

        // AND/OR: left child cannot have number P
        // (nodeType[p] = AND/OR) => (nodeChild[p] != P)
        for c in states {
            for k in states {
                if (1 <= P - 2) {
                    for p in 1...(P - 2) {
                        matrix.append(
                                (nodeType(c, k, p, NodeType.AND) | nodeType(c, k, p, NodeType.OR)) --> !nodeChild(c, k, p, P)
                        )
                    }
                }
            }
        }

        // AND/OR nodes have left child
        for c in states {
            for k in states {
                if (1 <= P - 2) {
                    for p in 1...(P - 2) {
                        matrix.append(
                                (nodeType(c, k, p, NodeType.AND) | nodeType(c, k, p, NodeType.OR)) --> !nodeChild(c, k, p, 0)
                        )
                    }
                }
            }
        }

        // TODO
        // AND/OR: hard to explain
        // parent[p, par] & nodetype[par, AND/OR] => child[par, p] | child[par, p-1]
//        for c in states {
//            for k in states {
//                for par in 1...P {
//                    // run {
//                    //                        val ch = par + 1
//                    //                        if (ch < P)
//                    //                            for (nt in listOf(NodeType.AND, NodeType.OR))
//                    //                                clause(
//                    //                                    nodeType[c, k, par] neq nt,
//                    //                                    nodeParent[c, k, ch] neq par,
//                    //                                    nodeChild[c, k, par] eq ch
//                    //                                )
//                    //                    }
//                    //                    for (ch in (par + 2) until P)
//                    //                        for (nt in listOf(NodeType.AND, NodeType.OR))
//                    //                            clause(
//                    //                                nodeType[c, k, par] neq nt,
//                    //                                nodeParent[c, k, ch] neq par,
//                    //                                nodeChild[c, k, par] eq ch,
//                    //                                nodeChild[c, k, par] eq ch - 1
//                    //                            )
//                }
//            }
//        }

        // Right child of binary operators follows the left one
        // (nodeType[p] = AND/OR) & (nodeChild[p] = ch) => (nodeParent[ch+1] = p)
        for c in states {
            for k in states {
                for p in 1...P {
                    for ch in 1..<P {
                        matrix.append(
                                ((nodeType(c, k, p, NodeType.AND) | nodeType(c, k, p, NodeType.OR)) & nodeChild(c, k, p, ch))
                                        --> nodeParent(c, k, ch + 1, p)
                        )
                    }
                }
            }
        }

        // NOT NODES CONSTRAINTS

        // NOT nodes cannot have number P
        for c in states {
            for k in states {
                if P >= 1 {
                    matrix.append(
                            !nodeType(c, k, P, NodeType.NOT)
                    )
                }
            }
        }

        // NOT nodes have left child
        for c in states {
            for k in states {
                for p in 1..<P {
                    matrix.append(
                            nodeType(c, k, p, NodeType.NOT) --> (!nodeChild(c, k, p, 0))
                    )
                }
            }
        }

        // NOT: parent's child is the current node
        // parent[p, par] & nodetype[par, NOT] => child[par, p]
        for c in states {
            for k in states {
                for p in 1...P {
                    for par in 1...P {
                        matrix.append(
                                (nodeParent(c, k, p, par) & nodeType(c, k, par, NodeType.NOT))
                                        --> nodeChild(c, k, par, p)
                        )
                    }
                }
            }
        }

        // NONE-TYPE NODES CONSTRAINTS

        // None-typed nodes do not have children
        for c in states {
            for k in states {
                for p in 1...P {
                    matrix.append(
                            nodeType(c, k, p, NodeType.NONE) --> nodeChild(c, k, p, 0)
                    )
                }
            }
        }

        // Terminal nodes have value from associated input variables
        // (nodeInputVariable[p] = x) => AND_{u}( nodeValue[p,u] <=> u[x] )
        // Done upper

        // AND: value is calculated as a conjunction of children values
        // (nodeType[p] = AND) & (nodeChild[p] = ch) =>
        //  AND_{u}( nodeValue[p,u] <=> nodeValue[ch,u] & nodeValue[ch+1,u] )
        // Done upper

        // OR: value is calculated as a disjunction of children values
        // (nodeType[p] = OR) & (nodeChild[p] = ch) =>
        //  AND_{u}( nodeValue[p,u] <=> nodeValue[ch,u] | nodeValue[ch+1,u] )
        // Done upper

        // NOT: value is calculated as a negation of a child value
        // (nodeType[p] = OR) & (nodeChild[p] = ch) =>
        //  AND_{u}( nodeValue[p,u] <=> ~nodeValue[ch,u] )
        // Done upper

        // None-type nodes have False values
        // (nodeType[p] = NONE) => AND_{u}( ~nodeValue[p,u] )
        // Done upper

        // Adhoc guard conditions constraints

        // Forbid double negation
        // (nodeType[p] = NOT) & (nodeChild[p] = ch) => (nodeType[ch] != NOT)
        for c in states {
            for k in states {
                for p in 1...P {
                    for ch in 1...P {
                        matrix.append(
                                (nodeType(c, k, p, NodeType.NOT) & nodeChild(c, k, p, ch)) --> !nodeType(c, k, ch, NodeType.NOT)
                        )
                    }
                }
            }
        }

        //
        //
        //

        let formula: Logic = matrix.reduce(Literal.True, &)

        var lambdas: [Proposition] = []
        for s in 0..<bound {
            for q in automaton.states {
                lambdas.append(lambda(s, q))
            }
        }
        var lambdaSharps: [Proposition] = []
        for s in 0..<bound {
            for q in automaton.states {
                lambdaSharps.append(lambdaSharp(s, q))
            }
        }
        var taus: [Proposition] = []
        for s in 0..<bound {
            for i in allBooleanAssignments(variables: inputPropositions) {
                taus += (0..<bound).map({ sPrime in tau(s, i, sPrime) })
            }
        }
        var outputPropositions: [Proposition] = []
        for o in specification.outputs {
            for s in 0..<bound {
                if specification.semantics == .mealy {
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        outputPropositions.append(Proposition(output(o, forState: s, andInputs: i)))
                    }
                } else {
                    outputPropositions.append(Proposition(output(o, forState: s)))
                }
            }
        }
        // Add Propositions to existential quantification
        var nodeTypes: [Proposition] = []
        var nodeChilds: [Proposition] = []
        var nodeParents: [Proposition] = []
        var nodeValues: [Proposition] = []
        var nodeAssignments: [Proposition] = []
        for c in states { // fromState: Int
            for k in states { // toState: Int
                for p in 0...P { // nodeIndex: Int
                    nodeTypes.append(nodeType(c, k, p, NodeType.TERMINAL))
                    nodeTypes.append(nodeType(c, k, p, NodeType.AND))
                    nodeTypes.append(nodeType(c, k, p, NodeType.OR))
                    nodeTypes.append(nodeType(c, k, p, NodeType.NOT))
                    nodeTypes.append(nodeType(c, k, p, NodeType.NONE))
                    for ch in 0...P {
                        nodeChilds.append(nodeChild(c, k, p, ch))
                        nodeParents.append(nodeParent(c, k, ch, p))
                    }
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        nodeValues.append(nodeValue(c, k, p, i))
                    }
                    for x in inputPropositions {
                        nodeAssignments.append(nodeAssignment(c, k, p, x))
                    }
                }
            }
        }

        let existentials: [Proposition] = lambdas + lambdaSharps + taus + outputPropositions
        + nodeTypes + nodeChilds + nodeParents + nodeValues + nodeAssignments

        var qbf: Logic = Quantifier(.Exists, variables: existentials, scope: formula)

        qbf = qbf.eval(assignment: initialAssignment)

        //print(qbf)

        let boundednessCheck = BoundednessVisitor()
        assert(qbf.accept(visitor: boundednessCheck))

        let removeComparable = RemoveComparableVisitor(bound: bound)
        qbf = qbf.accept(visitor: removeComparable)

        return qbf
    }

    func requireTransition(from s: Int, q: CoBüchiAutomaton.State, i: BooleanAssignment, qPrime: CoBüchiAutomaton.State, bound: Int, rejectingStates: Set<CoBüchiAutomaton.State>) -> Logic {
        let validTransition: [Logic]
        if automaton.isStateInNonRejectingSCC(q) || automaton.isStateInNonRejectingSCC(qPrime) || !automaton.isInSameSCC(q, qPrime) {
            // no need for comparator constrain
            validTransition = (0..<bound).map({
                sPrime in
                tauNextStateAssertion(state: s, i, nextState: sPrime, bound: bound) --> lambda(sPrime, qPrime)
            })
        } else {
            validTransition = (0..<bound).map({
                sPrime in
                tauNextStateAssertion(state: s, i, nextState: sPrime, bound: bound) -->
                        (lambda(sPrime, qPrime) & BooleanComparator(rejectingStates.contains(qPrime) ? .Less : .LessOrEqual, lhs: lambdaSharp(sPrime, qPrime), rhs: lambdaSharp(s, q)))
            })
        }
        return validTransition.reduce(Literal.True, &)
    }

    func tauNextStateAssertion(state: Int, _ inputs: BooleanAssignment, nextState: Int, bound: Int) -> Logic {
        return tau(state, inputs, nextState)
    }

    func lambda(_ state: Int, _ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition("λ_\(state)_\(automatonState)")
    }

    func lambdaSharp(_ state: Int, _ automatonState: CoBüchiAutomaton.State) -> Proposition {
        return Proposition("λ#_\(state)_\(automatonState)")
    }

    func tau(_ fromState: Int, _ inputs: BooleanAssignment, _ toState: Int) -> Proposition {
        return Proposition("τ_\(fromState)_\(bitStringFromAssignment(inputs))_\(toState)")
    }

    func eta(_ fromState: Int, _ toState: Int, _ nodeIndex: Int, _ nodeType: NodeType) -> Proposition {
        Proposition("η_\(fromState)_\(toState)_\(nodeIndex)_\(nodeType)")
    }

    func nodeType(_ fromState: Int, _ toState: Int, _ nodeIndex: Int, _ nodeType: NodeType) -> Proposition {
        eta(fromState, toState, nodeIndex, nodeType)
    }

    func sigma(_ fromState: Int, _ toState: Int, _ nodeIndex: Int, _ ch: Int) -> Proposition {
        Proposition("σ_\(fromState)_\(toState)_\(nodeIndex)_\(ch)")
    }

    func nodeChild(_ fromState: Int, _ toState: Int, _ nodeIndex: Int, _ ch: Int) -> Proposition {
        sigma(fromState, toState, nodeIndex, ch)
    }

    func pi(_ fromState: Int, _ toState: Int, _ nodeIndex: Int, _ p: Int) -> Proposition {
        Proposition("π\(fromState)_\(toState)_\(nodeIndex)_\(p)")
    }

    func nodeParent(_ fromState: Int, _ toState: Int, _ nodeIndex: Int, _ p: Int) -> Proposition {
        pi(fromState, toState, nodeIndex, p)
    }

    func nu(_ fromState: Int, _ toState: Int, _ nodeIndex: Int, _ inputs: BooleanAssignment) -> Proposition {
        Proposition("ν_\(fromState)_\(toState)_\(nodeIndex)_\(bitStringFromAssignment(inputs))")
    }

    func nodeValue(_ fromState: Int, _ toState: Int, _ nodeIndex: Int, _ inputs: BooleanAssignment) -> Proposition {
        nu(fromState, toState, nodeIndex, inputs)
    }

    func chi(_ fromState: Int, _ toState: Int, _ nodeIndex: Int, _ input: Proposition) -> Proposition {
        Proposition("χ_\(fromState)_\(toState)_\(nodeIndex)_\(input)")
    }

    func nodeAssignment(_ fromState: Int, _ toState: Int, _ nodeIndex: Int, _ input: Proposition) -> Proposition {
        chi(fromState, toState, nodeIndex, input)
    }

    func output(_ name: String, forState state: Int, andInputs inputs: BooleanAssignment? = nil) -> String {
        guard let inputs = inputs else {
            assert(specification.semantics == .moore)
            return "\(name)_\(state)"
        }
        assert(specification.semantics == .mealy)
        return "\(name)_\(state)_\(bitStringFromAssignment(inputs))"
    }


    mutating func solve(forBound bound: Int) throws -> Bool {
        Logger.default().info("build encoding for bound \(bound)")

        let constraintTimer = options.statistics?.startTimer(phase: .constraintGeneration)
        guard let instance = getEncoding(forBound: bound) else {
            throw BoSyEncodingError.EncodingFailed("could not build encoding")
        }
        constraintTimer?.stop()
        //print(instance)

        guard let solver = options.solver?.instance as? SatSolver else {
            throw BoSyEncodingError.SolvingFailed("solver creation failed")
        }

        let solvingTimer = options.statistics?.startTimer(phase: .solving)
        guard let result = solver.solve(formula: instance) else {
            throw BoSyEncodingError.SolvingFailed("solver failed on instance")
        }
        solvingTimer?.stop()

        if case .sat(let assignments) = result {
            // keep top level valuations of solver
            self.assignments = assignments
            self.solutionBound = bound
            return true
        }
        return false
    }

    func extractSolution() -> TransitionSystem? {
        let extractionTimer = options.statistics?.startTimer(phase: .solutionExtraction)
        let inputPropositions: [Proposition] = specification.inputs.map({ Proposition($0) })

        guard let assignments = assignments else {
            Logger.default().error("hasSolution() must be true before calling this function")
            return nil
        }

        var solution = ExplicitStateSolution(bound: solutionBound, specification: specification)
        for source in 0..<solutionBound {
            for target in 0..<solutionBound {
                var transitions: [Logic] = []
                for i in allBooleanAssignments(variables: inputPropositions) {
                    if assignments[tau(source, i, target)]! == Literal.False {
                        let clause = i.map({ v, val in val == Literal.True ? !v : v })
                        transitions.append(clause.reduce(Literal.False, |))
                    }
                }
                let transition = transitions.reduce(Literal.True, &)
                if transition as? Literal != nil && transition as! Literal == Literal.False {
                    continue
                }
                solution.addTransition(from: source, to: target, withGuard: transition)
            }
            for output in specification.outputs {
                let enabled: Logic
                switch specification.semantics {
                case .mealy:
                    var clauses: [Logic] = []
                    for i in allBooleanAssignments(variables: inputPropositions) {
                        let proposition = Proposition(self.output(output, forState: source, andInputs: i))
                        if assignments[proposition]! == Literal.False {
                            let clause = i.map({ v, val in val == Literal.True ? !v : v })
                            clauses.append(clause.reduce(Literal.False, |))
                        }
                    }
                    enabled = clauses.reduce(Literal.True, &)
                case .moore:
                    let proposition = Proposition(self.output(output, forState: source))
                    enabled = assignments[proposition]!
                }
                solution.add(output: output, inState: source, withGuard: enabled)
            }
        }
        extractionTimer?.stop()
        return solution
    }
}
