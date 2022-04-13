module bugTrackingSystem
open util/graph[Story]

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
	all story: bt.stories| some bt.recordedStories.story
	--all disj s1, s2: bt.stories | no univ.(recordedStories.s1) & univ.(recordedStories.s2) 
	
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
	all testcase: bt.testCases, description: bt.descriptions, failure: Failure | testcase -> description in bt.recordedDescT or failure -> description in bt.recordedDescF
	//all testcase: bt.testCases, stories: Story |  stories -> testcase in bt.recordedTestCases


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

--- FACTS
fact { all bt: BugTracking| inv[bt] }


--OPERATIONS
pred addStoryToFeature[preBT, postBT: BugTracking, feature: Feature, story: Story, priority: Priority] {
	//preconditions
	story not in preBT.stories  --story must not already exist
	feature in preBT.features --feature that the story is being added to must exist 
	story not in dom[preBT.storyOrder] + ran[preBT.storyOrder] --story not in story order 
	no preBT.recordedStories.story -- story not already associated with a feature

	//postconditions
	postBT.stories = preBT.stories + story --story must now exist
	dom[postBT.storyOrder] +ran [postBT.storyOrder] = (dom[preBT.storyOrder] +ran [preBT.storyOrder] ) + story --story must now exist in story order 
	story.(univ.recordedPriorityS) = priority --story must be recorded to have its set priority 
	story in feature.(postBT.recordedStories) --story must now be associated with the given story 
		
	//frameconditions
	preBT != postBT
	preBT.features = postBT.features
	preBT.failures = postBT.failures
	#preBT.testCases = #postBT.testCases
	preBT.inputs = postBT.inputs
	preBT.outputs = postBT.outputs
	preBT.descriptions = postBT.descriptions
}//run addStoryToFeature for 4 but 2 BugTracking expect 1


pred  addTestCaseToStory[preBT, postBT: BugTracking, feature: Feature, story: Story, testCase: TestCase, priority: Priority]{
	//preconditions
	story in preBT.stories  --story must already exist
	feature in preBT.features --feature that the story is being added to must exist 
	testCase not in preBT.testCases -- test case must not exist
	story in dom[preBT.storyOrder] + ran[preBT.storyOrder] --story in story order
	no preBT.recordedTestCases.testCase --test case must not be associated with any story
	//postconditions
	postBT.testCases = postBT.testCases + testCase --test case must now exist
	testCase in story.(postBT.recordedTestCases) -- test case is now associated with a story
	
	


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
//preBT, postBT: BugTracking, feature: Feature, story: Story, priority: Priority
	//preconditions
	resolution not in preBT.resolutions
	//instate should be unresolved
	//bt failure resolved
	some failure: preBT.failures, state: preBT.defaultStates | failure -> state in preBT.inState 

	failure -> resolution not in preBT.recordedResolution --resolution not already recorded
	some testcase: preBT.recordedFailures | some testcase.failure

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
	--story order shouldn't change
	

	

}run addResolutionToFailure for 4 but 2 BugTracking expect 1
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

