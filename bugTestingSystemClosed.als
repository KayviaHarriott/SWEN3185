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
	--all failure: bt.failures| some rf: bt.recordedFailures| failure in ran[rf]
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
	all testcase: bt.testCases, description: bt.descriptions, failure: Failure | testcase -> description in bt.recordedDescT or failure -> description in bt.recordedDescF
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
			some bt1, bt2: BugTracking, f: Feature,  s: Story, p: Priority, rr: Resolution, fai: Failure|
		skip[bt, btNext] or
			addStoryToFeature[bt1, bt2, f, s, p] or
				addResolutionToFailure[bt1, bt2, rr, fai] --or
					--Lucas's function
}run {} for 7 but 5 BugTracking expect 1


--OPERATIONS
pred addStoryToFeature[preBT, postBT: BugTracking, feature: Feature, story: Story, priority: Priority] {
	//preconditions
	story not in preBT.stories  --story must not already exist
	feature in preBT.features --feature that the story is being added to must exist 
	story not in dom[preBT.storyOrder] + ran[preBT.storyOrder] --story not in story order 
	feature -> story not in  preBT.recordedStories -- story not already associated with a feature
	story -> priority not in preBT.recordedPriorityS

	//postconditions
	postBT.stories = preBT.stories + story --story must now exist
	postBT.recordedStories = preBT.recordedStories + (feature -> story )
	dom[postBT.storyOrder] +ran [postBT.storyOrder] = (dom[preBT.storyOrder] +ran [preBT.storyOrder] ) + story --story must now exist in story order 
	story -> priority in postBT.recordedPriorityS
	
	
	--story.(univ.recordedPriorityS)= priority --story must be recorded to have its set priority 
	--feature -> story  in postBT.recordedStories --story must now be associated with the given story 
		
	//frameconditions
	preBT != postBT
	preBT.recordedFailures = postBT.recordedFailures
	preBT.recordedTestCases = postBT.recordedTestCases
	preBT.resolutions = postBT.resolutions
	preBT.testCases = postBT.testCases
	preBT.recordedDescF = postBT.recordedDescF
	preBT.actualOutput = postBT.actualOutput
	preBT.recordedDescT = postBT.recordedDescT
	preBT.recordedPriorityT = postBT.recordedPriorityT
	preBT.recordedActions = postBT.recordedActions
	preBT.recordedResolution = postBT.recordedResolution
	preBT.expectedOutput = postBT.expectedOutput
	preBT.recordedInput = postBT.recordedInput 
	preBT.inState = postBT.inState
}run addStoryToFeature for 4 but 2 BugTracking expect 1


pred  addTestCaseToStory[preBT, postBT: BugTracking, feature: Feature, story: Story, testCase: TestCase, priority: Priority]{
	//preconditions
	story in preBT.stories  --story must already exist
	feature in preBT.features --feature that the story is being added to must exist 
	testCase not in preBT.testCases -- test case must not exist
	story in dom[preBT.storyOrder] + ran[preBT.storyOrder] --story in story order
	//postconditions
	postBT.testCases = postBT.testCases + testCase --test case must now exist
	
	
	//frameconditions
	preBT != postBT
	preBT.features = postBT.features
	preBT.failures = postBT.failures
	#preBT.stories = #postBT.stories
	#preBT.features = #postBT.features
	
	

} run addTestCaseToStory for 4 but 2 BugTracking expect 1
	/*
		LUCAS UPDATE HERE
	*/

pred  addResolutionToFailure[preBT, postBT: BugTracking, resolution: Resolution, failure: Failure]{
	//preconditions
	resolution not in preBT.resolutions
	//instate should be unresolved
	//bt failure resolved
	some failure: preBT.failures, state: preBT.defaultStates | failure -> state in preBT.inState 

	failure -> resolution not in preBT.recordedResolution --resolution not already recorded
	---some testcase: preBT.recordedFailures | some testcase.failure

	//postconditions
	resolution in postBT.resolutions --resolution must now be in resolutions
	failure -> resolution in postBT.recordedResolution--must exist in recorded resolution
	some TestCase -> postBT.stories
	//frameconditions
	preBT != postBT
	preBT.features = postBT.features
	preBT.failures = postBT.failures
	#preBT.testCases = #postBT.testCases
	preBT.inputs = postBT.inputs
	preBT.outputs = postBT.outputs
	preBT.descriptions = postBT.descriptions
	preBT.stories= postBT.stories
	preBT.testCases = postBT.testCases
}run addResolutionToFailure for 4 but 2 BugTracking expect 1

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
		some bt.features
		some bt.stories
		some bt.testCases
		some bt.failures
		some bt.resolutions
		some bt.actions
		some bt.outputs 
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


assert addResolutionToFailurePreserves{
	all preBT, postBT: BugTracking,r: Resolution, f: Failure |
		inv[preBT] and addResolutionToFailure[preBT, postBT, r, f]
			implies inv[postBT]
} check addResolutionToFailurePreserves for 7 expect 0

-- FUNCTIONS

/* returns Pre(v) for vertex v in graph g */
fun pre[g: Story->Story, v: Story]: set Story {g.v}
run pre for 6

/* returns Post(v) for vertex v in graph g */
fun post[g: Story->Story, v: Story]: set Story {v.g}
run post for 6

