module bugTrackingSystem
open util/graph[Story]
open util/ordering[BugTracking] as bugT

// SYSTEM ELEMENTS
sig Feature, Story, TestCase, Failure, Resolution, Input,Output, Description, Action {}

abstract sig Priority {}
one sig Low, Medium, High extends Priority {}

abstract sig Severity {}
one sig Minor, Major, Critical extends Severity {}

abstract sig State {}
one sig Unresolved, WorkInProgress, Resolved extends State {}

abstract sig ReliabilityStatus {}
one sig A, B, C, D, E, F extends ReliabilityStatus {}


sig BugTracking{
	/*Relations*/
	features: set Feature,
	reliabilityStat: lone ReliabilityStatus,
	stories: set Story,
	testCases: set TestCase,
	failures: set Failure,
	resolutions: set Resolution,
	actions: set Action,
	defaultPriorities: set Priority,
	defaultSeverities: set Severity,
	defaultStates: set State,
	descriptions: set Description,
	inputs: set Input,
	outputs: set Output,
	
	/*Constraints*/
	recordedStories: features -> stories,
	storyOrder: stories->stories,
	recordedPriorityS: stories -> one defaultPriorities,
	recordedTestCases: stories -> testCases,

	recordedFailures: testCases -> failures,
	inState: failures -> one defaultStates,
	severityLev: failures -> one defaultSeverities,
	recordedResolution: failures -> lone resolutions,
	recordedActions: resolutions -> some actions,
	recordedDescF: failures -> descriptions,
	recordedPriorityT: testCases ->  defaultPriorities,
	recordedDescT: testCases ->  descriptions,

	actualOutput:  testCases -> one outputs,
	expectedOutput: testCases -> one outputs,
	recordedInput: testCases -> one inputs
}

--- PREDICATES
pred inv[bt: BugTracking]{ 
	all story: bt.stories| one bt.recordedStories.story
	
	all testcase: bt.testCases| some bt.recordedTestCases.testcase
	no disj t1,t2: bt.testCases | some recordedTestCases.t1 & recordedTestCases.t2
	
	all failure: bt.failures| some recordedFailures.failure 
	all res: bt.resolutions| some recordedResolution.res
	all disj r1,r2: bt.resolutions| no recordedResolution.r1 & recordedResolution.r2
	
	all action: bt.actions | some recordedActions.action
	
	all failure: bt.failures| one failure.(univ.recordedDescF)
	all testcase: bt.testCases| one testcase.(univ.recordedDescT)
	all testcase: bt.testCases, failure: bt.failures| failure.(univ.recordedDescF) != testcase.(univ.recordedDescT)
	no disj f1, f2: bt.failures| some f1.(univ.recordedDescF) &  f2.(univ.recordedDescF) 
	no disj t1, t2: bt.testCases| some t1.(univ.recordedDescT) &  t2.(univ.recordedDescT) 

	some bt.features implies one bt.reliabilityStat 
	no bt.features implies no bt.reliabilityStat 
	all description: bt.descriptions, failure: bt.failures, testcase: bt.testCases  | failure -> description in bt.recordedDescF or testcase -> description in bt.recordedDescT

	---
	all failure: bt.failures| failure.(univ.inState) = Resolved implies one failure.(univ.recordedResolution)
	all failure: bt.failures| failure.(univ.inState) != Resolved implies no failure.(univ.recordedResolution)

	all testcase: bt.testCases| testcase.(univ.expectedOutput) = testcase.(univ.actualOutput) implies no testcase.(univ.recordedFailures)
	all testcase: bt.testCases| testcase.(univ.expectedOutput) != testcase.(univ.actualOutput) implies some testcase.(univ.recordedFailures)

	let x = univ.storyOrder {
		tree[x]
		all n: innerNodes[x] + leaves[x] | #pre[x,n] <= 1
		all n: innerNodes[x] + roots[x] | #post[x, n] = 1
	}
}

private pred noChange1[preBT, postBT: BugTracking] {
	preBT.features = postBT.features
	preBT.reliabilityStat = postBT.reliabilityStat
	preBT.stories = postBT.stories
	preBT.testCases = postBT.testCases
	preBT.failures = postBT.failures
	preBT.resolutions = postBT.resolutions
	preBT.actions = postBT.actions
	preBT.defaultPriorities = postBT.defaultPriorities
	preBT.defaultSeverities = postBT.defaultSeverities
	preBT.defaultStates = postBT.defaultStates
	preBT.descriptions = postBT.descriptions
	preBT.inputs = postBT.inputs
	preBT.outputs = postBT.outputs
	preBT.recordedStories = postBT.recordedStories 
	preBT.storyOrder = postBT.storyOrder
	preBT.recordedPriorityS = postBT.recordedPriorityS
	preBT.recordedTestCases = postBT.recordedTestCases
	preBT.recordedFailures = postBT.recordedFailures
	preBT.inState = postBT.inState
	preBT.severityLev = postBT.severityLev
	preBT.recordedResolution = postBT.recordedResolution
	preBT.recordedActions = postBT.recordedActions
	preBT.recordedDescF = postBT.recordedDescF
	preBT.recordedPriorityT = postBT.recordedPriorityT
	preBT.recordedDescT = postBT.recordedDescT
	preBT.actualOutput = postBT.actualOutput
	preBT.expectedOutput = postBT.expectedOutput
	preBT.recordedInput = postBT.recordedInput 
}

pred skip[preBT, postBT: BugTracking] {
	noChange1[preBT, postBT]
}
run skip for 4 but 2 BugTracking expect 1
run skip for 4 but 1 BugTracking expect 1

--- FACTS
--fact { all bt: BugTracking| inv[bt] }

fact traces {
	init[bugT/first]
	inv[bugT/first]
	all bt: BugTracking - bugT/last |
		let btNext = bt.next |
			some bt1, bt2: BugTracking, f: Feature,  s: Story, p: Priority, rr: Resolution, fai: Failure, aa: Action, dd: Description, tt: TestCase, ss: State, rel: ReliabilityStatus|
		skip[bt, btNext] or
			addStoryToFeature[bt1, bt2, f, s, p] or
				addResolutionToFailure[bt1, bt2, rr, fai, aa, dd, tt, ss] or
					// feature: Feature, rel: ReliabilityStatus, story: Story
					addFeature [bt1, bt2, rr, fai, aa, dd, tt, ss, f, rel, s]--Lucas's function
}run {} for 7 but 5 BugTracking expect 1


--OPERATIONS
pred addStoryToFeature[preBT, postBT: BugTracking, feature: Feature, story: Story, priority: Priority] {
	//preconditions
	story not in preBT.stories  //story must not already exist
	feature in preBT.features //feature that the story is being added to must exist 
	story not in dom[preBT.storyOrder] + ran[preBT.storyOrder] //story not in story order 
	feature -> story not in  preBT.recordedStories // story not already associated with a feature
	story -> priority not in preBT.recordedPriorityS

	//postconditions
	postBT.stories = preBT.stories + story //story must now exist
	postBT.recordedStories = preBT.recordedStories + (feature -> story )
	dom[postBT.storyOrder] +ran [postBT.storyOrder] = (dom[preBT.storyOrder] +ran [preBT.storyOrder] ) + story //story must now exist in story order 
	story -> priority in postBT.recordedPriorityS
	story not in ran[preBT.recordedStories - feature -> story]
	story.(univ.recordedPriorityS)= priority //story must be recorded to have its set priority 
	feature -> story  in postBT.recordedStories //story must now be associated with the given story 
		
	//frameconditions
	preBT != postBT
	preBT.features = postBT.features
	preBT.reliabilityStat = postBT.reliabilityStat
	preBT.testCases = postBT.testCases
	preBT.failures = postBT.failures
	preBT.resolutions = postBT.resolutions
	preBT.actions = postBT.actions
	preBT.defaultPriorities = postBT.defaultPriorities
	preBT.defaultSeverities = postBT.defaultSeverities
	preBT.defaultStates = postBT.defaultStates
	preBT.descriptions = postBT.descriptions
	preBT.inputs = postBT.inputs
	preBT.outputs = postBT.outputs
	preBT.recordedTestCases = postBT.recordedTestCases
	preBT.recordedFailures = postBT.recordedFailures
	preBT.inState = postBT.inState
	preBT.severityLev = postBT.severityLev
	preBT.recordedResolution = postBT.recordedResolution
	preBT.recordedActions = postBT.recordedActions
	preBT.recordedDescF = postBT.recordedDescF
	preBT.recordedPriorityT = postBT.recordedPriorityT
	preBT.recordedDescT = postBT.recordedDescT
	preBT.actualOutput = postBT.actualOutput
	preBT.expectedOutput = postBT.expectedOutput
	preBT.recordedInput = postBT.recordedInput 
}run addStoryToFeature for 4 but 2 BugTracking expect 1




pred  addResolutionToFailure[preBT, postBT: BugTracking, resolution: Resolution, failure: Failure, action: Action, description: Description, testcase: TestCase, state: State]{
	//preconditions
	resolution not in preBT.resolutions -- the resolution should not exist in the resolutions
	failure -> resolution not in preBT.recordedResolution -- must not already exist in recorded resolution
	resolution not in dom[preBT.recordedActions] -- resolution must not be in recordedResolutions
	//testcase -> description in preBT.recordedDescT -- all test cases have description
//	failure -> description in preBT.recordedDescF -- all failures should have description
	 -- inState should not be resolved
	
	//some failure: preBT.failures, state: preBT.defaultStates | failure -> state in preBT.inState 
	

	//postconditions
	postBT.resolutions= preBT.resolutions+resolution
	resolution in postBT.resolutions -- the resolution should exist in the resolutions
	failure -> resolution in postBT.recordedResolution -- must exist in recorded resolution
	resolution -> action in postBT.recordedActions -- resolution must be in recordedResolutions
	-- inState should be 'Resolved'
	#postBT.recordedResolution = add[#preBT.recordedResolution, 1]

	//frameconditions
	preBT != postBT --before and after state of the system should not be the same
	preBT.features = postBT.features
	preBT.failures = postBT.failures
	preBT.stories= postBT.stories
	preBT.reliabilityStat = postBT.reliabilityStat
	preBT.testCases = postBT.testCases
	preBT.failures = postBT.failures
	preBT.actions = postBT.actions
	preBT.defaultPriorities = postBT.defaultPriorities
	preBT.defaultSeverities = postBT.defaultSeverities
	preBT.defaultStates = postBT.defaultStates
	preBT.descriptions = postBT.descriptions
	preBT.inputs = postBT.inputs
	preBT.outputs = postBT.outputs
		preBT.recordedTestCases = postBT.recordedTestCases 
		preBT.recordedFailures = postBT.recordedFailures
	--	preBT.inState != postBT.inState
	preBT.severityLev = postBT.severityLev 
	preBT.recordedDescF = postBT.recordedDescF
		preBT.recordedDescT = postBT.recordedDescT
		preBT.actualOutput = postBT.actualOutput
		preBT.expectedOutput = postBT.expectedOutput
		preBT.recordedInput = postBT.recordedInput 
	preBT.recordedStories = postBT.recordedStories 
	preBT.storyOrder = postBT.storyOrder
	

	

}run addResolutionToFailure for 4 but 2 BugTracking expect 1
	/*
		Given a Failure whose state is not being changed to resolved, we want to add the resolution to that failure so as to 
			1. not violate our invariants
			2. record the resolution that has caused the failure to be resolved
		To do this we need the pre and post state, the failure, the resolution and the actions taken to arrive at that resolution
	*/


pred  addFeature[preBT, postBT: BugTracking, resolution: Resolution, failure: Failure, action: Action, description: Description, testcase: TestCase, state: State, feature: Feature, rel: ReliabilityStatus, story: Story]{
	//preconditions
	feature not in preBT.features-- feature does not exist
	

	//postconditions
	postBT.features = preBT.features + feature-- feature added to system
	feature in postBT.features-- feature does exist
	


	//frameconditions
	preBT != postBT-- before and after state of system not the same
	 


	--preBT.features = postBT.features features: set Feature,
	--preBT.reliabilityStat = postBT.reliabilityStat 
	--#preBT.features != #postBT.features
	preBT.stories = postBT.stories
	preBT.testCases = postBT.testCases
	preBT.failures = postBT.failures
	preBT.resolutions = postBT.resolutions
	preBT.actions = postBT.actions
	preBT.defaultPriorities = postBT.defaultPriorities
	preBT.defaultSeverities = postBT.defaultSeverities
	preBT.defaultStates = postBT.defaultStates
	preBT.descriptions = postBT.descriptions
	preBT.inputs = postBT.inputs
	preBT.outputs = postBT.outputs
	
	preBT.storyOrder = postBT.storyOrder
	preBT.recordedPriorityS = postBT.recordedPriorityS
	preBT.recordedTestCases = postBT.recordedTestCases
	preBT.recordedFailures = postBT.recordedFailures
	preBT.inState = postBT.inState
	preBT.severityLev = postBT.severityLev
	preBT.recordedResolution = postBT.recordedResolution
	preBT.recordedActions = postBT.recordedActions
	preBT.recordedDescF = postBT.recordedDescF
	preBT.recordedPriorityT = postBT.recordedPriorityT
	preBT.recordedDescT = postBT.recordedDescT

	

}run addFeature for 4 but 2 BugTracking expect 1
	/*
		Given a Failure whose state is not being changed to resolved, we want to add the resolution to that failure so as to 
			1. not violate our invariants
			2. record the resolution that has caused the failure to be resolved
		To do this we need the pre and post state, the failure, the resolution and the actions taken to arrive at that resolution
	*/
-- INSTANCES

pred init [bt: BugTracking] {
	some features
	some bt.reliabilityStat
	some stories
	some testCases
	some failures
	some resolutions
	some actions
	some defaultPriorities
	some defaultSeverities
	some defaultStates
	some descriptions
	some inputs
	some outputs
	some recordedStories
	some storyOrder
	some recordedPriorityS
	some recordedTestCases
	some recordedFailures
	some inState
	some severityLev
	some recordedResolution
	some recordedActions
	some recordedDescF
	some recordedPriorityT
	some recordedDescT
	some actualOutput
	some expectedOutput
	some recordedInput}
run init for 7 but 1 BugTracking expect 1

pred sanityCheck{
	some bt: BugTracking{
		#bt.features = 2
		#bt.stories = 3
		#bt.testCases = 2	
		#bt.failures > 2
		#bt.resolutions > 2
		#bt.actions > 2
		#bt.outputs = 2
	}
} run sanityCheck for 6 but 1 BugTracking expect 1


--ASSERTIONS
assert initEstablishes{
	all bt: BugTracking| init[bt] implies inv[bt]
}check initEstablishes

assert addStoryToFeaturePreserves{
	all preBT, postBT: BugTracking, f: Feature, s: Story, p: Priority  |
		inv[preBT] and addStoryToFeature[preBT, postBT, f, s, p]
			implies inv[postBT]
} check addStoryToFeaturePreserves for 7 expect 0

//addTestCaseToStory[preBT, postBT: BugTracking, feature: Feature, story: Story, testCase: TestCase, priority: Priority]
assert addResolutionToFailurePreserves{
	all preBT, postBT: BugTracking,r: Resolution, f: Failure, a: Action, d: Description, t: TestCase, s: State |
		inv[preBT] and addResolutionToFailure[preBT, postBT, r, f, a, d, t, s]
			implies inv[postBT]
} check addResolutionToFailurePreserves for 7 expect 0


--addFeature[preBT, postBT: BugTracking, resolution: Resolution, failure: Failure, action: Action, description: Description, testcase: TestCase, state: State, feature: Feature, rel: ReliabilityStatus, story: Story]
assert addFeature{
	all preBT, postBT: BugTracking,r: Resolution, f: Failure, a: Action, d: Description, t: TestCase, s: State, fe: Feature, rel: ReliabilityStatus, story: Story |
		inv[preBT] and addFeature[preBT, postBT, r, f, a, d, t, s, fe, rel, story]
			implies inv[postBT]
} check addFeature for 7 expect 0 /**/


-- FUNCTIONS

/* returns Pre(v) for vertex v in graph g */
fun pre[g: Story->Story, v: Story]: set Story {g.v}
run pre for 6

/* returns Post(v) for vertex v in graph g */
fun post[g: Story->Story, v: Story]: set Story {v.g}
run post for 6

