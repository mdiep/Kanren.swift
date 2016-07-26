
struct Variable: CustomStringConvertible, Hashable {
    let index: UInt
    var description: String { return "#\(index)" }
    var hashValue: Int { return Int(index) }
}

func ==(lhs: Variable, rhs: Variable) -> Bool {
    return lhs.index == rhs.index
}

indirect enum Term<Value: Equatable>: CustomStringConvertible, Equatable {
    case variable(Variable)
    case value(Value)
    case pair(Term<Value>, Term<Value>)
    case empty
    
    var description: String {
        switch self {
        case let .variable(v):       return v.description
        case let .value(v):          return "\(v)"
        case let .pair(left, right): return "(\(left), \(right))"
        case .empty:                 return "()"
        }
    }
    
    init<C: Collection where C.Iterator.Element == Term<Value>>(_ collection: C) {
        var iterator = collection.reversed().makeIterator()
        var term = Term.empty
        while let next = iterator.next() {
            term = Term.pair(next, term)
        }
        self = term
    }
}

extension Term: ArrayLiteralConvertible {
    init(arrayLiteral elements: Term<Value>...) {
        self = .init(elements)
    }
}

func == <Value>(lhs: Term<Value>, rhs: Term<Value>) -> Bool {
    switch (lhs, rhs) {
    case let (.variable(lhs), .variable(rhs)):
        return lhs == rhs
    case let (.value(lhs), .value(rhs)):
        return lhs == rhs
    case let (.pair(lhs1, lhs2), .pair(rhs1, rhs2)):
        return lhs1 == rhs1 && lhs2 == rhs2
    case (.empty, .empty):
        return true
    default:
        return false
    }
}

struct UnificationError: ErrorProtocol { }

struct State<Value: Equatable>: CustomStringConvertible {
    typealias Goal = (State<Value>) -> AnyIterator<State<Value>>
    
    var substitution: [Variable: Term<Value>] = [:]
    var counter: UInt = 0
    
    var variables: [Variable] {
        return (0..<counter).map { Variable(index: $0) }
    }
    
    var description: String {
        return variables
            .map { v in
                let value = walk(.variable(v))
                if .variable(v) == value {
                    return "\(v)"
                } else {
                    return "\(v) = \(value)"
                }
            }
            .joined(separator: ", ")
    }
    
    /// ext-s
    func extend(_ variable: Variable, _ term: Term<Value>) -> State {
        var state = self
        state.substitution[variable] = term
        return state
    }
    
    /// walk
    func walk(_ term: Term<Value>) -> Term<Value> {
        if case let .variable(variable) = term, let value = substitution[variable] {
            return walk(value)
        } else if case let .pair(left, right) = term {
            return .pair(walk(left), walk(right))
        } else {
            return term
        }
    }
    
    /// unify
    func unify(_ a: Term<Value>, _ b: Term<Value>) throws -> State<Value> {
        let a = walk(a)
        let b = walk(b)
        
        if a == b { return self }
        
        switch (a, b) {
        case let (.variable(a), _):
            return extend(a, b)
        case let (_, .variable(b)):
            return extend(b, a)
        case let (.pair(a1, a2), .pair(b1, b2)):
            return try unify(a1, b1).unify(a2, b2)
        default:
            throw UnificationError()
        }
    }
}

func == <Value>(lhs: Term<Value>, rhs: Term<Value>) -> State<Value>.Goal {
    return { state in
        do {
            return AnyIterator(values: [ try state.unify(lhs, rhs) ])
        } catch {
            return AnyIterator(values: [])
        }
    }
}

func == <Value>(lhs: Variable, rhs: Variable) -> State<Value>.Goal {
    return .variable(lhs) == .variable(rhs)
}

func == <Value>(lhs: Variable, rhs: Value) -> State<Value>.Goal {
    return .variable(lhs) == .value(rhs)
}

func || <Value>(lhs: State<Value>.Goal, rhs: State<Value>.Goal) -> State<Value>.Goal {
    return { state in lhs(state).interleave(with: rhs(state)) }
}

func && <Value>(lhs: State<Value>.Goal, rhs: State<Value>.Goal) -> State<Value>.Goal {
    return { state in lhs(state).flatMap(rhs) }
}

func fresh<Value>(block: (Variable) -> State<Value>.Goal) -> State<Value>.Goal {
    return { state in
        var state = state
        let variable = Variable(index: state.counter)
        state.counter += 1
        return block(variable)(state)
    }
}

func fresh<Value>(block: (Variable, Variable) -> State<Value>.Goal) -> State<Value>.Goal {
    return fresh { x in fresh { y in { state in block(x, y)(state) } } }
}

func fresh<Value>(block: (Variable, Variable, Variable) -> State<Value>.Goal) -> State<Value>.Goal {
    return fresh { x in fresh { y in fresh { z in { state in block(x, y, z)(state) } } } }
}

let goal1 = fresh { a, b in
    a == 7 && (a == b || b == 6)
}
let iter1 = goal1(State())
iter1.next()
iter1.next()
iter1.next()

let goal2 = fresh { x, y, z in
    [.variable(x), .value(4), .variable(z)] == [.value(1), .variable(y), .value(3)]
}
let iter2 = goal2(State())
iter2.next()
iter2.next()

func append<Value>(_ head: Term<Value>, _ tail: Term<Value>, _ list: Term<Value>) -> State<Value>.Goal {
    return (head == .empty && tail == list)
        || fresh { first, restOfHead, restOfList in
            return head == .pair(.variable(first), .variable(restOfHead))
                && list == .pair(.variable(first), .variable(restOfList))
                && append(.variable(restOfHead), tail, .variable(restOfList))
    }
}

let goal3 = fresh { x in
    append([.value("h"), .value("e")], [.value("l"), .value("l"), .value("o")], .variable(x))
}
let iter3 = goal3(State())
iter3.next()
iter3.next()
