from z3 import *
from Data.precis_feature import PrecisFeature
from Data.feature_vector import FeatureVector
from Data.precis_formula import PrecisFormula
from Learners.houdini import Houdini
from featurizer import Featurizer
from Learners.feature_synthesis import FeatureSynthesis
from os import sys
from typing import List, Tuple, Type
import math
import numpy
import logging


logger = logging.getLogger("Results.DisjunctiveLearner")

class DisjunctiveLearner:

    # entropy measure is used by default for choosing Predicates to split data on
    # for now we choose, largest entropy
    useEntropy = True
    featureSynthesizer = None
    
    def __init__(self, featureSynthesizer, entropy=True):
        self.useEntropy = entropy
        self.featureSynthesizer = featureSynthesizer 

    def synthesizeUniqueFeatures(self, intBaseFeat, boolBaseFeat, baseFeatureValues, exclude):
        syntFeats : Tuple[PrecisFeature] = self.featureSynthesizer.synthesizeFeatures(intBaseFeat, boolBaseFeat, baseFeatureValues)  
        # if boolBaseFeat empty, no derived bool features will be generated -> consider refactor
        genFeats : Tuple[PrecisFeature] = self.featureSynthesizer.GenerateDerivedFeatures(intBaseFeat, boolBaseFeat) 
        derivFeats : Tuple[PrecisFeature] = Featurizer.mergeSynthesizedAndGeneratedFeatures(syntFeats, genFeats)
        uniqueDerivFeats = tuple([f for f in derivFeats if f not in exclude])
        return uniqueDerivFeats

    def learn4(self, k, intBaseFeat, boolBaseFeat, baseFeatureValues, exclude, solver, call):
        #on the empty set of data points, return true
        if len(baseFeatureValues) == 0:
            print("called learn4 with 0 feature vectors")
            logger.info("called learn4 with 0 feature vectors")
            return PrecisFormula(BoolVal(False))
        #rename  splitIntoBoolAndIntFeatureVectors
        (intBaseFeatVectors, boolBaseFeatVectors) = Featurizer.getBoolAndIntFeatureVectors(intBaseFeat, boolBaseFeat, baseFeatureValues)

        derivFeats = self.synthesizeUniqueFeatures(intBaseFeat, boolBaseFeat, baseFeatureValues, exclude)
        derivFeatVectors: List[FeatureVector] = Featurizer.generateDerivedFeatureVectors(derivFeats, intBaseFeat+boolBaseFeat,baseFeatureValues )
        #assert(len(baseFeatureValues) == len(derivFeatVectors))
        boolFvs = Featurizer.mergeFeatureVectors(boolBaseFeatVectors,derivFeatVectors)
        boolFeatures = boolBaseFeat + derivFeats
        boolFeatToReturn = set(boolFeatures)
        #boolFeatToReturn = boolFeatToReturn.union(allBoolFeatures)
        houdini = Houdini()
        (allTrueFormula, indicesAllwaysTrue, conjuncts) = houdini.learn4(boolFeatures , boolFvs, call)
        
        print("common conjuction: k="+str(k)+" "+allTrueFormula.toInfix())
        logger.info("Houdini AlwaysTrue for k="+str(k)+" : "+ allTrueFormula.toInfix()+"\n")
        smtConjunct = "true"
        if len(conjuncts) != 0:
            smtConjunct = "(and "+ ' '.join([ pFeat.varName for pFeat in  conjuncts]) + ")"

        if k == 0:
            return allTrueFormula, boolFeatToReturn, smtConjunct
        else:
            #removing features returned by houdini and their corresponding feature vector entries. 
            (remainingBaseBoolFeat, remainingDerivBoolFeat, featuresRemoved)  = \
                self.removeFeatureFromFeaturelist(boolBaseFeat, derivFeats, indicesAllwaysTrue)
            
            (reaminingEntriesBaseBoolFv, reaminingEntriesDerivBoolFv) = \
                self.removeFeatureEntryInFeatureVectors(boolBaseFeatVectors, derivFeatVectors, indicesAllwaysTrue)
            
            # features that are true on parent node should not be passed down to children;(they are redundantly also true in child nodes)
            exclude = exclude + featuresRemoved
            lookAhead = len(intBaseFeatVectors[0])
            
            ######################################
            #bug: chooseFeatureImplication does not update reamining bool features or feature vectors. Idx is with respect to updates
            #solver = Solver()
            solver.add(allTrueFormula.formulaZ3 == BoolVal(True))
            solver.push()
            (f,idx, posBaseFv, negBaseFv, remainingBaseBoolFeat, remainingDerivBoolFeat ) = \
                self.chooseFeatureImplication(allTrueFormula,intBaseFeat,remainingBaseBoolFeat , remainingDerivBoolFeat, \
                    Featurizer.mergeFeatureVectors(intBaseFeatVectors,reaminingEntriesBaseBoolFv) , reaminingEntriesDerivBoolFv, lookAhead, solver, call )
            ######################################
            if idx < 0:
                print("Predicate: "+ call + " for k = "+ str(k)+" : None")
                logger.info("Predicate: "+ call + " for k = "+ str(k)+" : None"+"\n")
                return allTrueFormula, boolFeatToReturn, smtConjunct
            #TODO: choose should return boolBasePosFv and intBasePosFv ...
            #(f,idx, posBaseFv, negBaseFv) = \
            #    self.chooseFeature2(remainingBaseBoolFeat + remainingDerivBoolFeat, \
            #        Featurizer.mergeFeatureVectors(intBaseFeatVectors,reaminingEntriesBaseBoolFv), reaminingEntriesDerivBoolFv, call, lookAhead)
            logger.info("Predicate: "+ call + " for k = "+ str(k)+" : "+ str(f)+"\n")
            print("Predicate: "+ call+" : "+str(f))
            
            #featureSplitRemoved == f 
            (newBoolBaseFeat, newDeriveBaseFeat, featureSplitRemoved) = \
                self.removeFeatureFromFeaturelist(remainingBaseBoolFeat, remainingDerivBoolFeat, [idx])
            # if predicate to split on is in derivedFeatures, then add to exclude list; 
            if len(remainingBaseBoolFeat) == len(newBoolBaseFeat):
                exclude = exclude + (f,)
            else:
                # if predicate to split is in baseFeatures, the update posBaseFv and negBaseFv feature vectors
                posBaseFv = self.removeFeatureEntryInBaseFv(posBaseFv,[idx+lookAhead])
                negBaseFv = self.removeFeatureEntryInBaseFv(negBaseFv,[idx+lookAhead])
            #push(allTrue)
            posPost, boolFeatToReturnPos, smtPos = self.learn4( k-1,\
                intBaseFeat, newBoolBaseFeat, posBaseFv, exclude, solver, call + " Left")  #recursive call
            
            logger.info(call +" Left: " + " for k = "+ str(k)+" : "+ posPost.toInfix())
            print(call +" Left: " + " for k = "+ str(k)+" : "+ posPost.toInfix())

            negPost, boolFeatToReturnNeg, smtNeg = self.learn4( k-1,\
                intBaseFeat, newBoolBaseFeat, negBaseFv, exclude, solver, call +" Right") #recursive call
            
            solver.pop()
            unionOfSubTrees = boolFeatToReturnPos.union(boolFeatToReturnNeg)
            allUniqueBoolFeat = boolFeatToReturn.union(unionOfSubTrees) 
            logger.info(call +" Right: " + " for k = "+ str(k)+" : "+ negPost.toInfix())
            print(call +" Right: " + " for k = "+ str(k)+" : "+ negPost.toInfix())
            postSmt = "(and "+ smtConjunct +" "+ "(ite "+f.varName +" "+ smtPos+" "+smtNeg +"))"
            disjunctivePost  = And(allTrueFormula.formulaZ3, Or(And(posPost.formulaZ3, f.varZ3), And(negPost.formulaZ3, Not(f.varZ3) )))
            precisPost = PrecisFormula(disjunctivePost)
            return precisPost, allUniqueBoolFeat, postSmt

    #baseFeartureVectors : List of lists but the inner list are FeatureVector datatype
    def learn3(self, k, intBaseFeat, boolBaseFeat, baseFeatureValues, exclude, solver, call):
        #on the empty set of data points, return true
        if len(baseFeatureValues) == 0:
            print("called learn3 with 0 feature vectors")
            logger.info("called learn3 with 0 feature vectors")
            return PrecisFormula(BoolVal(False))
        #rename  splitIntoBoolAndIntFeatureVectors
        (intBaseFeatVectors, boolBaseFeatVectors) = Featurizer.getBoolAndIntFeatureVectors(intBaseFeat, boolBaseFeat, baseFeatureValues)

        derivFeats = self.synthesizeUniqueFeatures(intBaseFeat, boolBaseFeat, baseFeatureValues, exclude)
        derivFeatVectors: List[FeatureVector] = Featurizer.generateDerivedFeatureVectors(derivFeats, intBaseFeat+boolBaseFeat,baseFeatureValues )
        #assert(len(baseFeatureValues) == len(derivFeatVectors))
        boolFvs = Featurizer.mergeFeatureVectors(boolBaseFeatVectors,derivFeatVectors)
        
        houdini = Houdini()
        (allTrueFormula, indicesAllwaysTrue) = houdini.learn2(boolBaseFeat + derivFeats , boolFvs, call)
        logger.info("Houdini AlwaysTrue for k="+str(k)+" : "+ allTrueFormula.toInfix()+"\n")
        
        if k == 0:
            return allTrueFormula
        else:
            #removing features returned by houdini and their corresponding feature vector entries. 
            (remainingBaseBoolFeat, remainingDerivBoolFeat, featuresRemoved)  = \
                self.removeFeatureFromFeaturelist(boolBaseFeat, derivFeats, indicesAllwaysTrue)
            
            (reaminingEntriesBaseBoolFv, reaminingEntriesDerivBoolFv) = \
                self.removeFeatureEntryInFeatureVectors(boolBaseFeatVectors, derivFeatVectors, indicesAllwaysTrue)
            
            # features that are true on parent node should not be passed down to children;(they are redundantly also true in child nodes)
            exclude = exclude + featuresRemoved
            lookAhead = len(intBaseFeatVectors[0])
            
            ######################################
            #bug: chooseFeatureImplication does not update reamining bool features or feature vectors. Idx is with respect to updates
            #solver = Solver()
            solver.add(allTrueFormula.formulaZ3 == BoolVal(True))
            solver.push()
            (f,idx, posBaseFv, negBaseFv, remainingBaseBoolFeat, remainingDerivBoolFeat ) = \
                self.chooseFeatureImplication(allTrueFormula,intBaseFeat,remainingBaseBoolFeat , remainingDerivBoolFeat, \
                    Featurizer.mergeFeatureVectors(intBaseFeatVectors,reaminingEntriesBaseBoolFv) , reaminingEntriesDerivBoolFv, lookAhead, solver, call )
            ######################################
            if idx < 0:
                print("Predicate: "+ call + " for k = "+ str(k)+" : None")
                logger.info("Predicate: "+ call + " for k = "+ str(k)+" : None"+"\n")
                return allTrueFormula
            #TODO: choose should return boolBasePosFv and intBasePosFv ...
            #(f,idx, posBaseFv, negBaseFv) = \
            #    self.chooseFeature2(remainingBaseBoolFeat + remainingDerivBoolFeat, \
            #        Featurizer.mergeFeatureVectors(intBaseFeatVectors,reaminingEntriesBaseBoolFv), reaminingEntriesDerivBoolFv, call, lookAhead)
            logger.info("Predicate: "+ call + " for k = "+ str(k)+" : "+ str(f)+"\n")
            print("Predicate chosen at "+ call+" : "+str(f))
            
            #featureSplitRemoved == f 
            (newBoolBaseFeat, newDeriveBaseFeat, featureSplitRemoved) = \
                self.removeFeatureFromFeaturelist(remainingBaseBoolFeat, remainingDerivBoolFeat, [idx])
            # if predicate to split on is in derivedFeatures, then add to exclude list; 
            if len(remainingBaseBoolFeat) == len(newBoolBaseFeat):
                exclude = exclude + (f,)
            else:
                # if predicate to split is in baseFeatures, the update posBaseFv and negBaseFv feature vectors
                posBaseFv = self.removeFeatureEntryInBaseFv(posBaseFv,[idx+lookAhead])
                negBaseFv = self.removeFeatureEntryInBaseFv(negBaseFv,[idx+lookAhead])
            #push(allTrue)
            posPost = self.learn3( k-1,\
                intBaseFeat, newBoolBaseFeat, posBaseFv, exclude, solver, call + " Left")  #recursive call
            
            logger.info(call +" Left: " + " for k = "+ str(k)+" : "+ posPost.toInfix())
            print(call +" Left: " + " for k = "+ str(k)+" : "+ posPost.toInfix())

            negPost = self.learn3( k-1,\
                intBaseFeat, newBoolBaseFeat, negBaseFv, exclude, solver, call +" Right") #recursive call
            
            solver.pop()

            logger.info(call +" Right: " + " for k = "+ str(k)+" : "+ negPost.toInfix())
            print(call +" Right: " + " for k = "+ str(k)+" : "+ negPost.toInfix())

            disjunctivePost  = And(allTrueFormula.formulaZ3, Or(And(posPost.formulaZ3, f.varZ3), And(negPost.formulaZ3, Not(f.varZ3) )))
            precisPost = PrecisFormula(disjunctivePost)
            return precisPost

    #Features only contains bool features
    def chooseFeatureImplication(self, alwaysTrueFormula, intBaseFeatures, baseBoolFeatures, \
         derivBoolFeatures, baseFv, derivFv, lookAhead, solver, call ):
        houdini = Houdini()
        fvPos = list()
        fvPosDeriv = list()
        fvNeg = list()
        fvNegDeriv = list()
        irrelevantFeatures = ()
        irrelevantIndices = []
        boolFeatures = baseBoolFeatures + derivBoolFeatures
        for idx in range(0, len(boolFeatures)):
            #region pruneFunction
            feature = boolFeatures[idx]
            if is_int(feature.varZ3):
                assert(False)
            (fvPos,fvPosDeriv,fvNeg,fvNegDeriv) = self.splitSamplesImplication(feature, idx + lookAhead, baseFv, derivFv)
            #if len(fvPos) == 0 or len(fvNeg) == 0:
                #irrelevantIndices.append(idx)
                #continue
            
            (posIntBaseFv, posBoolBaseFv) = Featurizer.getBoolAndIntFeatureVectors(intBaseFeatures, baseBoolFeatures, fvPos)
            (negIntBaseFv, negBoolBaseFv) = Featurizer.getBoolAndIntFeatureVectors(intBaseFeatures, baseBoolFeatures, fvNeg)

            posFvs = Featurizer.mergeFeatureVectors(posBoolBaseFv, fvPosDeriv)
            negFvs = Featurizer.mergeFeatureVectors(negBoolBaseFv, fvNegDeriv)
            #consider adding check to not call houdini with empty list of posFvs or negFvs
            (posAllTrueFormula, posIndicesAllwaysTrue, conjunctsPos) = houdini.learn4(boolFeatures , posFvs, call+" implication check-- bad split pred "+str(feature))
            (negAllTrueFormula, negIndicesAllwaysTrue, conjunctsNeg) = houdini.learn4(boolFeatures , negFvs, call+" implication check-- bad split pred "+str(feature))
            if (is_true(posAllTrueFormula.formulaZ3) and len(negFvs) == 0) or (is_true(negAllTrueFormula.formulaZ3) and len(posFvs) == 0):
                print(call+ " implication check-- bad split pred: "+ str(feature))
                irrelevantIndices.append(idx)
                continue
           
            if len(fvPos) != 0 and len(fvNeg) != 0:
                print(call+ " implication check-- good split pred: "+ str(feature))
                logger.info(call+ " implication check-- split pred: "+ str(feature))
                logger.info(call+ " implication check-- featurePos: "+ str(posAllTrueFormula.toInfix()))
                logger.info(call+ " implication check-- featureNeg: "+ str(negAllTrueFormula.toInfix())+"\n")
                
                
            #disjunct z3 type
            disjunct = Or(And(posAllTrueFormula.formulaZ3, feature.varZ3 ) , And(negAllTrueFormula.formulaZ3, Not(feature.varZ3)))
           
            implication = Implies(alwaysTrueFormula.formulaZ3 , disjunct)
            #solver = Solver()
            # check (not (postK0 => postK1)) is unsat -- validity check
            solver.add(Not(implication))
            #logger.info("smt format:\n"+ solver.to_smt2())
            check = solver.check()
            #splitting on `feature does not` add new information: alwaysTrueFormula -> (OR(f and posSplit, ~f and negSplit)) is valid
            if str(check) == 'unsat':
                #collect irrelevant features and indices to remove
                irrelevantFeatures = irrelevantFeatures + (feature,)
                irrelevantIndices.append(idx)
            #splitting adds new information
            elif str(check) == 'sat':
                print("passed implication check: "+ feature.varName)
                pass
            else:
                # solver does not know
                assert(False)
            #endregion
        
        copyBaseIntFeat = tuple(intBaseFeatures)
        copyBaseBoolFeat = tuple(baseBoolFeatures)
        copyDerivFeat = tuple(derivBoolFeatures)
        #(remainingBaseBoolFeat, remainingDerivBoolFeat, featuresRemoved)  = \
        #    self.removeFeatureFromFeaturelist(boolBaseFeat, derivFeats, indicesAllwaysTrue)
        (intBaseFv, boolBaseFv) = Featurizer.getBoolAndIntFeatureVectors(copyBaseIntFeat, copyBaseBoolFeat, baseFv)
        
        (copyRemainingBaseBoolFeat, copyRemainingDerivBoolFeat, featuresRemoved) = \
            self.removeFeatureFromFeaturelist(copyBaseBoolFeat, copyDerivFeat, irrelevantIndices)

        #boolFvs = Featurizer.mergeFeatureVectors(boolBaseFv, derivFv)
        (copyReaminingEntriesBaseBoolFv, reaminingEntriesDerivBoolFv) = \
            self.removeFeatureEntryInFeatureVectors(boolBaseFv, derivFv, irrelevantIndices)
        #Debug Check
        if (len(copyRemainingBaseBoolFeat) + len(copyRemainingDerivBoolFeat)) == 0:
            return (None, -1,None, None, None, None)
        skipAhead = len(intBaseFv[0])
        newBaseFv = Featurizer.mergeFeatureVectors(intBaseFv,copyReaminingEntriesBaseBoolFv)

        (f,idx, posBaseFv, negBaseFv) = self.chooseFeature2(copyRemainingBaseBoolFeat + copyRemainingDerivBoolFeat,newBaseFv,reaminingEntriesDerivBoolFv, call, skipAhead)
        #print(irrelevantIndices)
        
        #intBaseFeatures = copyBaseIntFeat
        #baseBoolFeatures = copyRemainingBaseBoolFeat
        #erivBoolFeatures = copyDerivFeat
        #baseFv = newBaseFv
        #derivFv = reaminingEntriesDerivBoolFv
        return (f, idx, posBaseFv, negBaseFv, copyRemainingBaseBoolFeat, copyRemainingDerivBoolFeat)

        # f is for feature of PrecisFeature type
    def splitSamplesImplication(self, f, idx, baseFv, derivFv):
        posF = list()
        posFDeriv = list()
        negF = list()
        negFDeriv = list()
        if len(baseFv) == 0:
            assert(False)
        #assert(len(baseFv)== len(derivFv))
        fv = baseFv
        if idx >= len(baseFv[0]):
            idx = idx - len(baseFv[0])
            fv = derivFv
        # add assertion check that every entry  in feature vector, fv, in list, featureVectors, is of type z3.z3.BoolRef
        # is_true(True) returns False; True is a python boolean expression. is_true(BoolVal(True)) returns True 
        #print(len(featureVectors))
        for idxFv in range(0, len(fv)):
            if is_true(fv[idxFv][idx]):
                posF.append(baseFv[idxFv])
                posFDeriv.append(derivFv[idxFv])
            elif is_int(fv[idxFv][idx]):
                assert(False)
            else:
                negF.append(baseFv[idxFv])
                negFDeriv.append(derivFv[idxFv])
        
        #assert(len(baseFv) == len(posF)+ len(negF))
        return (posF,posFDeriv,negF,negFDeriv)


    def chooseFeature2(self, features, baseFv, derivFv, call, skipAhead):
        # TODO: figure is removing always false predicates will lead to optimizations
        fvPos = list()
        fvNeg = list()
        allScores = []
        for idx in range(0, len(features)):
            if is_int(features[idx].varZ3):
                assert(False)
            (fvPos, fvNeg, score, rank) = self.scoreFeature2(features[idx], idx, baseFv, derivFv, skipAhead)
            allScores.append({'predicate': features[idx],'idx': idx, 'score': score, 'rank':rank , 'posData':fvPos, 'negData': fvNeg} )
            
        sortedScores = sorted(allScores, key=lambda x: (x['score'], x['rank']))
        #consider adding a case to check if chosen predicate is always false (i.e., score == 0) should return negative index.
        return (sortedScores[-1]['predicate'], sortedScores[-1]['idx'], sortedScores[-1]['posData'], sortedScores[-1]['negData']) 
    
    def scoreFeature2(self, f, idx, baseFv, derivFv, skipAhead):
        (fvPos, fvNeg) = self.splitSamples(f, idx + skipAhead, baseFv, derivFv) 
  
        if len(fvPos) == 0 or len(fvNeg) == 0:
            score = 0
        else:
            assert(len(fvPos) != 0)
            assert(len(fvNeg) != 0)
            score = self.scoreE(len(fvPos), len(fvNeg))
        astLength = len(f.varZ3.children()) + 1.0
        rank = (score / astLength )
        
        return (fvPos, fvNeg, score, rank)

    # f is for feature of PrecisFeature type
    def splitSamples(self, f, idx, baseFv, derivFv):
        posF = list()
        negF = list()
        if len(baseFv) == 0:
            assert(False)
        #assert(len(baseFv)== len(derivFv))
        fv = baseFv
        if idx >= len(baseFv[0]):
            idx = idx - len(baseFv[0])
            fv = derivFv
        # add assertion check that every entry  in feature vector, fv, in list, featureVectors, is of type z3.z3.BoolRef
        # is_true(True) returns False; True is a python boolean expression. is_true(BoolVal(True)) returns True 
        #print(len(featureVectors))
        for idxFv in range(0, len(fv)):
            if is_true(fv[idxFv][idx]):
                posF.append(baseFv[idxFv])
            elif is_int(fv[idxFv][idx]):
                assert(False)
            else:
                negF.append(baseFv[idxFv])
        
        #assert(len(baseFv) == len(posF)+ len(negF))
        return (posF, negF)

        #return feature along with index

    #baseFv -> feature vector with only boolean entries
    def chooseFeature(self, features, baseFv, derivFv, call, skipAhead):
        # TODO: figure is removing always false predicates will lead to optimizations
        fvPos = list()
        fvNeg = list()
        
        allScores = []
        for idx in range(0, len(features)):
            if is_int(features[idx].varZ3):
                assert(False)
            (fvPos, fvNeg) = self.splitSamples(features[idx], idx + skipAhead, baseFv, derivFv) 
            #skip always false predicates
            #if len(fvPos) == 0 and len(fvNeg)> 0:
            #    continue
            #posLabel = ['+'] * len(fvPos)
            #negLabel = ['-'] * len(fvNeg)
            #score = self.entropy(posLabel+negLabel)
            
            if len(fvPos) == 0 or len(fvNeg) == 0:
                score = 0
            else:
                assert(len(fvPos) != 0)
                assert(len(fvNeg) != 0)
                score = self.scoreE(len(fvPos), len(fvNeg))
                #score = self.entropy(posLabel+negLabel)
            astLength = len(features[idx].varZ3.children()) + 1.0
            rank = (score / astLength )
            allScores.append({'predicate': features[idx],'idx': idx, 'score': score ,'rank':rank , 'posData':fvPos, 'negData': fvNeg} )
            
        # ranking by x['score'] + x['rank'] is wrong; 
        # Feature oldContainsX is chosen over New_x == Old_Top even though New_x == Old_Top is correct.
        sortedScores = sorted(allScores, key=lambda x: (x['score'], x['rank']))
        return (sortedScores[-1]['predicate'], sortedScores[-1]['idx'], sortedScores[-1]['posData'], sortedScores[-1]['negData']) 


    def scoreE(self,l1, l2):
        l3 = l1 + l2
        return -1*(((l1/l3)*(math.log(l1/l3)/math.log(math.e))) + ((l2/l3)* (math.log(l2/l3)/math.log(math.e))))

    # labels is a list of all class labels 
    def entropy(self, labels, base = None):
        valueLabel, occurrencesLabel = numpy.unique(labels, return_counts=True)
        currentTotalSample = occurrencesLabel.sum()
        probability_value_attribute = numpy.true_divide(occurrencesLabel, currentTotalSample )
        base = math.e if base is None else base
        #debug code
        denominator = numpy.log(base)
        rightNumerator = numpy.log(probability_value_attribute)
        numerator = probability_value_attribute * rightNumerator
        fraction = (numerator / numpy.log(base)) # why divide by numpy.log(base) -> numpy.log(e)==1
        #end debug code
        return - (probability_value_attribute * numpy.log(probability_value_attribute) / numpy.log(base)).sum()
        # Note: I believe this implementation is missing an additional multiplication
        #return - ((probability_value_attribute/initialTotalSample)* probability_value_attribute * numpy.log(probability_value_attribute) / numpy.log(base)).sum()

    def removeFeatureEntryInBaseFv(self ,baseFvs, indices):
        newBaseFvs = list()
        if len(baseFvs) == 0:
            assert(False)
        # len(baseFvs) == len(derivFvs) should hold when this function is called
        #numOfFvs = len(baseFvs)
        if all(indices[i] <= indices[i+1] for i in range(len(indices)-1)):
            for idxFV in range(0, len(baseFvs)):
                newBaseFv = FeatureVector.copyFeatureVector(baseFvs[idxFV])
                
                for idx in reversed(indices):
                    if idx >= len(baseFvs[idxFV]):
                        assert(False)
                    else:
                        newBaseFv.values = newBaseFv.values[0:idx] + newBaseFv.values[idx+1:]
                        newBaseFv.valuesZ3 = newBaseFv.valuesZ3[0:idx] + newBaseFv.valuesZ3[idx+1:]
                        
                newBaseFvs.append(newBaseFv)
                
        else:
            assert(False)
        return newBaseFvs

    #fix this
    def removeFeatureEntryInFeatureVectors(self,baseFvs, derivFvs, indices):
        newBaseFvs = list()
        newDerivFvs = list()
        if len(baseFvs) == 0:
            assert(False)
        # len(baseFvs) == len(derivFvs) should hold when this function is called
        #numOfFvs = len(baseFvs)
        if all(indices[i] <= indices[i+1] for i in range(len(indices)-1)):
            #for idx in reversed(indices):
            for idxFV in range(0, len(baseFvs)):
                derivIdx =-2
                newDerivFv = FeatureVector.copyFeatureVector(derivFvs[idxFV])
                newBaseFv = FeatureVector.copyFeatureVector(baseFvs[idxFV])
                
                for idx in reversed(indices):
                    if idx >= len(baseFvs[idxFV]):
                        #compute new index for removing entry in derivFV
                        derivIdx = idx - len(baseFvs[idxFV]) 
                        newDerivFv.values = newDerivFv.values[0:derivIdx] + newDerivFv.values[derivIdx+1:]
                        newDerivFv.valuesZ3 = newDerivFv.valuesZ3[0:derivIdx] + newDerivFv.valuesZ3[derivIdx+1:]
                    else:
                        newBaseFv.values = newBaseFv.values[0:idx] + newBaseFv.values[idx+1:]
                        newBaseFv.valuesZ3 = newBaseFv.valuesZ3[0:idx] + newBaseFv.valuesZ3[idx+1:]
                        
                newBaseFvs.append(newBaseFv)
                newDerivFvs.append(newDerivFv)
        else:
            assert(False)
        return (newBaseFvs, newDerivFvs)

    
    def removeFeatureFromFeaturelist(self,baseFeatures,derivFeatures,indices):
        
        newBaseFeatures = tuple(baseFeatures)
        newDerivFeatures = tuple(derivFeatures)
        featuresRemoved = ()
        if all(indices[i] <= indices[i+1] for i in range(len(indices)-1)):
            for idx in reversed(indices):
                #removing from derived features
                if idx >= len(baseFeatures):
                    idx = idx - len(baseFeatures)
                    featuresRemoved = featuresRemoved + (newDerivFeatures[idx],)
                    newDerivFeatures = newDerivFeatures[0:idx]+ newDerivFeatures[idx+1:]
                # removing from base features
                else:
                    featuresRemoved = featuresRemoved + (newBaseFeatures[idx],)
                    newBaseFeatures = newBaseFeatures[0:idx]+ newBaseFeatures[idx+1:]
        else:
            assert(False)
        
        return (newBaseFeatures, newDerivFeatures, featuresRemoved)

if __name__ == '__main__':

    #PrecisFeature: def __init__(self, isDerived, varName, varType=None, isNew=None, varZ3=None):

    feature1 = PrecisFeature(False, "New_Containsx", "BOOL", "New_Containsx".startswith("New_"), None)