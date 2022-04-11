module bugTrackingSystem
open util/graph[Story]

// SYSTEM ELEMENTS
sig System { allFeatures: set Feature, reliabilityStat: lone ReliabilityStatus }

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
	all story: bt.stories| some recordedStories.story
	--all disj s1, s2: bt.stories | no univ.(recordedStories.s1) & univ.(recordedStories.s2) 
	
	all testcase: bt.testCases| some recordedTestCases.testcase
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


-- FUNCTIONS

/* returns Pre(v) for vertex v in graph g */
fun pre[g: Story->Story, v: Story]: set Story {g.v}
run pre for 6

/* returns Post(v) for vertex v in graph g */
fun post[g: Story->Story, v: Story]: set Story {v.g}
run post for 6

