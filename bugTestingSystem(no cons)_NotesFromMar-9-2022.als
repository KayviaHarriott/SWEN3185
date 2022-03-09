module bugTrackingSystem

// SYSTEM ELEMENTS
//one sig System { TPs: seq TestPackage, reliabilityStat: one ReliabilityStatus }
sig System { allFeatures: set Feature, reliabilityStat: lone ReliabilityStatus }
//when doing an instance of the system you can run for 1 instance of the System, or the System set contains 
//one thing
//be able to create a system without a feature, so 
//createFact: if a system has atleast one feature it must have a reliability status

sig Feature {stories: set Story, orderedStories: stories -> stories}
//It's possible for it[stories] to be ordered or graphed, paths in the mapping of stories tells you
//the ordering, think if it's Hamiltonian paths -yes


abstract sig Priority {}
one sig Low, Medium, High extends Priority {}

abstract sig Severity {}
one sig Minor, Major, Critical extends Severity {}

abstract sig State {}
one sig Unresolved, WorkInProgress, Resolved extends State {}

abstract sig ReliabilityStatus {}
one sig VeryLow extends ReliabilityStatus {}//, Low, Medium, High, VeryHigh 
//someway to measure it

//could have a description 
//Calculator and I want to add negative numbers
sig Story {
	testCases: set TestCase, 
	//note disj set is an oxymoron
	priorityLevel: one Priority
}


sig TestCase {
	priorityLevel: one Priority, 
	desc: Description, 
//if you don't put a multiplicity it still means one, one is the default
	inputs: some Input,
	expectedOutput: one Output,
	actualOutput: one Output,
	fails: Failure
//fault could lead to a failure
}

sig Failure {
	severityLevel: one Severity, 
	resolution: lone Resolution, 
	description: one Description, 
	state: one State
}

sig Input,Output, Description, Resolution {}



//FACTS
//breaking down resolution into the set of actions, maybe sig actions, and may contain
//an empty set, we can talk about similarities of test case resolution and for instance
//same things down to resolve a test case but one has one of high and one of low, why should that be?
//could say one test case is common with another one and resolution may apply to two test cases
//no two testCases should have the same description

fact uniqueDescriptionForEachTestCase{
	no disj testCaseA, testCaseB : TestCase | some testCaseA.desc & testCaseB.desc
}

//there should be no test case that is not related to a story 
//for every test case there must be some story that has it associated with it
fact noLooseTestCase{
	all testCase: TestCase|some s:Story| testCase in s.testCases 
}

//a story can only belong to one feature
fact storyOnlyOneFeature{
	all story: Story | one feat: Feature | story in feat.stories
} 

//each story should belong to a feature 
fact noLooseStory{
	all story: Story | some feat: Feature| story in feat.stories
}

//no two stories should share any test cases
fact noSameTestCaseforStory{
	all disj storyA,storyB: Story | no storyA.testCases & storyB.testCases
}

//A failure should only be related to one testcase
fact oneTestCaseforaFailure{
	all failure: Failure | one testCase: TestCase | failure in testCase.fails
}

//no feature should be disconnected from the system
fact noLooseFeature{
	all feature: Feature | one system: System | feature in system.allFeatures
}

//no shared descriptions between testcases and failures
fact noTestCaseAndFailureSameDescription{
	all testCase: TestCase, fails: Failure | no testCase.desc & fails.description
}

//no two failures can have the same description - Kayvia
fact uniqueFailureDescription{
	all disj failure1,failure2: Failure | no failure1.description & failure2.description
}

//all resolutions should be associated with a failure
fact allResolutionsHaveFailure{
	all res: Resolution | some fail: Failure | res in fail.resolution
}

fact ifResolvedHAsResolution{
	all failure: Failure| failure.state ! = Resolved implies #failure.resolution = 0
}


// FUNCTIONS
fun getTestPackage[f :Feature]: set TestCase{
	f.stories.testCases
}

//PREDICATES

//Instance of all relations in the model
pred sanityCheck {
	one System
	#Feature = 2
	#Story  = 3
	#TestCase> 3
	some Input
	some Output 
	some Failure
	some Description
	some Resolution} 
run sanityCheck for 5

//instance where there is a story that has more than two test cases and more than two failures
pred anInstance[s:Story]{
	# s.testCases > 2
	#s.testCases.fails > 2
}run anInstance for 6 but 1 System

//instance where there is a system with three features and atleast 3 stories have been written
pred anInstance2[sys: System]{
	#sys.allFeatures = 2
	#sys.allFeatures.stories > 2
}run anInstance2 for 5
