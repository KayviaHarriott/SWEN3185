module bugTrackingSystem
open util/graph[Story]

// SYSTEM ELEMENTS
sig System { allFeatures: set Feature, reliabilityStat: lone ReliabilityStatus }

sig Feature {stories: set Story, orderedStories: stories -> stories}

abstract sig Priority {}
one sig Low, Medium, High extends Priority {}

abstract sig Severity {}
one sig Minor, Major, Critical extends Severity {}

abstract sig State {}
one sig Unresolved, WorkInProgress, Resolved extends State {}

abstract sig ReliabilityStatus {}
one sig A, B, C, D, E, F extends ReliabilityStatus {}

sig Story {
	testCases: set TestCase, 
	priorityLevel: Priority
}

sig TestCase {
	priorityLevel: Priority, 
	desc: Description, 
	inputs: some Input,
	expectedOutput: Output,
	actualOutput: Output,
	failures: set Failure
}

sig Failure {
	severityLevel: Severity, 
	resolution: lone Resolution, 
	description: Description, 
	state: State
}
sig Resolution{
	ResActions: some Action
}

sig Input,Output, Description, Action {}


-- FACTS

//English - each story should belong to a feature 
fact noLooseStory{
	all story: Story | some feat: Feature| story in feat.stories
}

//English - a story can only belong to one feature
fact storyOnlyOneFeature{
	all disj featureA,featureB: Feature | no featureA.stories & featureB.stories 
} 

//English - for every test case there must be some story that owns it
fact noLooseTestCase{
	all testCase: TestCase|some s:Story| testCase in s.testCases 
}

//English - no two stories should share any test cases
fact noSameTestCaseforStory{
	all disj storyA,storyB: Story | no storyA.testCases & storyB.testCases
}

//English - no feature should be disconnected from the system
fact noLooseFeature{
	all feature: Feature | one system: System | feature in system.allFeatures
}

//English - a failure should only be related to one testcase
fact oneTestCaseforaFailure{
	all failure: Failure | one testCase: TestCase | failure in testCase.failures
}

//English - if a system has at least one feature it must have a reliability status
fact hasReliabilityStatIfHasFeature{
	all sys: System| {
		some sys.allFeatures implies one sys.reliabilityStat
		no sys.allFeatures implies #sys.reliabilityStat = 0
	}
}

//English - if a failure has a state of Resolved, there must be a resolution associated with the failure
fact ifResolvedHAsResolution{
	all failure: Failure|{
		failure.state ! = Resolved implies  no failure.resolution
		failure.state = Resolved implies one failure.resolution
	}
}

//English - all resolutions should be associated with a failure
fact allResolutionsHaveFailure{
	all res: Resolution | some fail: Failure | res in fail.resolution
}

//English - for all test cases, the description should be unique i.e. no test cases may have the same description
fact uniqueDescriptionForEachTestCase{
	no disj testCaseA, testCaseB : TestCase | some testCaseA.desc & testCaseB.desc
}

//English - no shared descriptions between testcases and failures
fact noTestCaseAndFailureSameDescription{
	all testCase: TestCase, fails: Failure | no testCase.desc & fails.description
}

//fact {all feature: Feature| 
//	isHamiltonianPath[feature.stories, feature.orderedStories]
//}

-- PREDICATES

//Instance of all relations in the model
pred sanityCheck {
	one System
	#Feature = 2
	#Story  = 3
	#TestCase = 3
	#Input = 2
	#Output = 2
	#Failure > 3
	some failure: Failure | failure.state = Unresolved
	some Description
	some Resolution} 
run sanityCheck for 6 but 1 System

//instance where there is a story that has more than two test cases and more than two failures
pred anInstance[s:Story]{
	#s.testCases > 2
	#s.testCases.failures > 2
}run anInstance for 6 but 1 System

//instance where there is a system with three features and atleast 3 stories have been written
pred anInstance2[sys: System]{
	#sys.allFeatures = 2
	#sys.allFeatures.stories > 2
}run anInstance2 for 5 but 1 System

pred anInstance3[]{
	one System
	no Feature
}run anInstance3 for 5 but 1 System


pred isHamiltonianPath  [s: set Story , ms: Story -> Story] {
	#Story  =  5 
	tree[ms]
	all n: innerNodes[ms] + leaves[ms] | #pre[ms, n] <= 1
	all n: innerNodes[ms] + roots[ms] | #post[ms, n] = 1
}
run isHamiltonianPath for 10 but 1 System


-- FUNCTIONS

/* returns Pre(v) for vertex v in graph g */
fun pre[g: Story->Story, v: Story]: set Story {g.v}
run pre for 6

/* returns Post(v) for vertex v in graph g */
fun post[g: Story->Story, v: Story]: set Story {v.g}
run post for 6

