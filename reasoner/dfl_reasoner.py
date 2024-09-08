from knowrob import *

import dfl.dlquery as dl

def _iriOrVariable(reasoner, x):
    def _cleanStr(x):
        for c in ["'", '"']:
            while c == x[0]:
                x = x[1:]
                if c == x[-1]:
                    x = x[:-1]
        return str(x)
    if x.isVariable():
        return x
    return IRIAtom(reasoner.expandName(_cleanStr(repr(x))))

class SOMADFLReasoner(GoalDrivenReasoner):
    def __init__(self):
        super().__init__()
        self.reasoner = dl.DFLReasoner()
        self.hasDisposition = IRIAtom("http://www.ease-crc.org/ont/SOMA_DFL.owl#hasDisposition")
        self.isDispositionOf = IRIAtom("http://www.ease-crc.org/ont/SOMA_DFL.owl#isDispositionOf")
        self.hasPart = IRIAtom("http://www.ease-crc.org/ont/SOMA_DFL.owl#hasPart")
        self.isPartOf = IRIAtom("http://www.ease-crc.org/ont/SOMA_DFL.owl#isPartOf")
        self.hasConstituent = IRIAtom("http://www.ease-crc.org/ont/SOMA_DFL.owl#hasConstituent")
        self.isConstituentOf = IRIAtom("http://www.ease-crc.org/ont/SOMA_DFL.owl#isConstituentOf")
        self.useMatch = PredicateIndicator("http://www.ease-crc.org/ont/SOMA_DFL.owl#useMatch", 3)
        self.isInstanceOf = IRIAtom("http://www.ease-crc.org/ont/SOMA_DFL.owl#isInstanceOf")
        self.isSubclassOf = IRIAtom("http://www.ease-crc.org/ont/SOMA_DFL.owl#isSubclassOf")
        self.rdfType = IRIAtom("http://www.w3.org/1999/02/22-rdf-syntax-ns#type")
        self.defineRelation(self.hasDisposition)
        self.defineRelation(self.hasPart)
        self.defineRelation(self.hasConstituent)
        self.defineRelation(self.isDispositionOf)
        self.defineRelation(self.isPartOf)
        self.defineRelation(self.isConstituentOf)
        self.defineRelation(self.useMatch)
        self.defineRelation(self.isInstanceOf)
        self.defineRelation(self.isSubclassOf)
        self.simpleGoals = {self.hasPart, self.hasConstituent, self.hasDisposition, self.isDispositionOf, self.isPartOf, self.isConstituentOf, self.isInstanceOf, self.isSubclassOf}
        self.inverseProperties = {self.isDispositionOf: self.hasDisposition, self.isPartOf: self.hasPart, self.isConstituentOf: self.hasConstituent}
        self.fnMap = {self.hasDisposition: lambda g, p, s, o, bounding: self._evaluateSimpleGoal(g, p, s, o, bounding, self.reasoner.whatDispositionsDoesObjectHave, self.reasoner.whatHasDisposition),
                      self.hasPart: lambda g, p, s, o, bounding: self._evaluateSimpleGoal(g, p, s, o, bounding, self.reasoner.whatPartTypesDoesObjectHave, self.reasoner.whatHasPartType),
                      self.hasConstituent: lambda g, p, s, o, bounding: self._evaluateSimpleGoal(g, p, s, o, bounding, self.reasoner.whatConstituentsDoesObjectHave, self.reasoner.whatHasConstituent),
                      self.isSubclassOf: lambda g, p, s, o, bounding: self._evaluateIsSubclassOf(g, p, s, o, bounding),
                      self.isInstanceOf: lambda g, p, s, o, bounding: self._evaluateSimpleGoal(g, p, s, o, bounding, self._ensureIndividual2Classes, self._ensureClass2Individuals)}
        self.classes = set([self.reasoner.expandName(x) for x in self.reasoner.whatSubclasses('owl:Thing')])
        
    def _evaluateIsSubclassOf(self, goal, p, s, o, bounding):
        if ((False, True) == bounding):
            v = o
            retq = self.reasoner.whatSuperclasses(self.reasoner.expandName(str(s)))
        else:
            v = s
            retq = self.reasoner.whatSubclasses(self.reasoner.expandName(str(o)))
        for sc in retq:
            bdgs = Binding()
            bdgs.set(v, IRIAtom(self.reasoner.expandName(sc)))
            goal.push(bdgs)
        return True

    def _evaluateSimpleGoal(self, goal, p, s, o, bounding, fnOVar, fnSVar):
        if ((False, True) == bounding):
            todo = self._ensureIndividual2Classes(s)
            dispositions = set().union(*[fnOVar(str(c)) for c in todo])
            for d in dispositions:
                bdgs = Bindings()
                bdgs.set(o, IRIAtom(self.reasoner.expandName(d)))
                goal.push(bdgs)
        else:
            concepts = [self.reasoner.expandName(c) for c in fnSVar(str(o))]
            instances = set().union(*[self._ensureClass2Individuals(c) for c in concepts])
            if ((True, False) == bounding):
                for i in instances:
                    bdgs = Bindings()
                    bdgs.set(s, IRIAtom(self.reasoner.expandName(i)))
                    goal.push(bdgs)
            elif ((False, False) == bounding) and str(s) in instances:
                goal.push(Bindings())
        return True

    def _ensureIndividual2Classes(self, entity):
        entity = str(entity)
        entity = self.reasoner.expandName(entity)
        retq = [entity]
        if entity not in self.classes:
            query_term = GraphSequence([GraphPattern(IRIAtom(entity), self.rdfType, Variable("Z"))])
            retq = []
            self.storage().query(GraphQuery(query_term), lambda bindings : retq.append(bindings.get(Variable("Z"))))
            retq = list(set().union(*[self.reasoner.whatSuperclasses(str(c)) for c in retq]))
        return retq
        
    def _ensureClass2Individuals(self, entity):
        entity = str(entity)
        entity = self.reasoner.expandName(entity)
        retq = [entity]
        if entity in self.classes:
            retq = set()
            for sc in self.reasoner.whatSubclasses(str(entity)):
                sc = self.reasoner.expandName(sc)
                query_term = GraphSequence([GraphPattern(Variable("Z"), self.rdfType, IRIAtom(sc))])
                self.storage().query(GraphQuery(query_term), lambda bindings : retq.add(str(bindings.get(("Z")))))
                #self.storage().query(GraphQuery(query_term), lambda bindings : True)
            retq = list(retq)
        return retq
                
    def initializeReasoner(self, config: PropertyTree) -> bool:
        # TODO: parse and use config.
        # Flags that would make sense:
        #     ontology and usematch files to use
        #     namespace prefixes
        self.reasoner.initializeOntology()
        self.classes = set([self.reasoner.expandName(x) for x in self.reasoner.whatSubclasses("owl:Thing")])
        return True

    def evaluate(self, goal: Goal) -> bool:
        # Assume only simple goals for now.
        literal = goal.formula().literals()[0].predicate()
        p = _iriOrVariable(self.reasoner, literal.functor())
        if p in self.simpleGoals:
            s : Term = _iriOrVariable(self.reasoner, literal.arguments()[0])
            o : Term = _iriOrVariable(self.reasoner, literal.arguments()[1])
            logWarn("Checking %s(%s, %s)" % (str(p), str(s), str(o)))
            args = [x for x in [s, o] if not x.isVariable()]
            if p in self.inverseProperties:
                p = self.inverseProperties[p]
                x = s
                s = o
                o = x
            bounding = (s.isVariable(), o.isVariable())
            if (True, True) == bounding:
                raise ValueError("Must specify at least one of the participants in the %s goal." % str(p))
            self.fnMap[p](goal, p, s, o, bounding)
        else: # useMatch goal
            task : Term = _iriOrVariable(self.reasoner, literal.arguments()[0])
            instrument : Term = _iriOrVariable(self.reasoner, literal.arguments()[1])
            patient : Term = _iriOrVariable(self.reasoner, literal.arguments()[2])
            # TODO: maybe implement questions of type "what could I do with these objects"
            if task.isVariable():
                raise ValueError("Task must be specified for useMatch query")
            bounding = tuple([x.isVariable() for x in [instrument, patient]])
            # TODO: maybe implement questions of type "are there any objects around I could use for task?"
            if (True, True) == bounding:
                raise ValueError("Must specify at least one of patient or instrument in a useMatch query")
            if ((False, True) == bounding):
                todo = self._ensureIndividual2Classes(instrument)
                classes = set().union(*[self.reasoner.whatObjectsCanToolPerformTaskOn(str(task), c) for c in todo])
                classes = [self.reasoner.expandName(c) for c in classes]
                instances = set().union(*[self._ensureClass2Individuals(c) for c in classes])
                for i in instances:
                    bdgs = Bindings()
                    bdgs.set(instrument, IRIAtom(self.reasoner.expandName(i)))
                    goal.push(bdgs)

            else:
                todo = self._ensureIndividual2Classes(patient)
                classes = set().union(*[self.reasoner.whatToolsCanPerformTaskOnObject(str(task), c) for c in todo])
                classes = [self.reasoner.expandName(c) for c in classes]
                instances = set().union(*[self._ensureClass2Individuals(c) for c in classes])
                if (True, False) == bounding:
                    for i in instances:
                        bdgs = Bindings()
                        bdgs.set(instrument, IRIAtom(self.reasoner.expandName(i)))
                        goal.push(bdgs)
                elif ((False, False) == bounding) and (str(instrument) in instances):
                    goal.push(Bindings())
        return True # False: reasoning error









'''
            fn = self.fnMap.get(str(p),{}).get(bounding)
            if fn is None:
                raise AttributeError("Query not implemented yet for predicate %s and bounding pattern %s" % (str(p), str(bounding)))
            fn(*args)
            #query_term = GraphSequence([
            #    GraphPattern(s, self.loves, Variable("z")),
            #    GraphPattern(o, self.loves, Variable("z")),
            #    GraphBuiltin.notEqual(s, o)])
            #self.storage().query(GraphQuery(query_term), goal.push)
        return True
'''     
