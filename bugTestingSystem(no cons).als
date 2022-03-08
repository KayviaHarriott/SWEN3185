module bugTrackingSystem

// SYSTEM ELEMENTS
//one sig System { TPs: seq TestPackage, reliabilityStat: one ReliabilityStatus }
one sig System { allFeatures: some Feature, reliabilityStat: one ReliabilityStatus }

sig Feature {stories: set Story}

abstract sig Priority {}
one sig Low, Medium, High extends Priority {}

abstract sig Severity {}
one sig Minor, Major, Critical extends Severity {}

abstract sig State {}
one sig Unresolved, WorkInProgress, Resolved extends State {}

//could have a description 
//Calculator and I want to add negative numbers
sig Story {
	testCases: disj set TestCase, 
	priorityLevel: one Priority
}

sig TestCase {
	priorityLevel: one Priority, 
	desc: disj one Description, 
	inputs: some Input,
	expectedOutput: one Output,
	faults: set Failure
}

sig Failure {
	severityLevel: one Severity, 
	resolution: lone Resolution, 
	description: one Description, 
	state: one State
} 

sig Input,Output, Description, Resolution, ReliabilityStatus {}

//FACTS

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
	all failure: Failure | one testCase: TestCase | failure in testCase.faults
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
//fact uniqueFailureDescription{
	//all disj failure1,failure2: Failure | no failure1.description & failure2.description
//}


// FUNCTIONS
fun getTestPackage[f :Feature]: set TestCase{
	f.stories.testCases
}

//Instance of all relations in the model
pred sanityCheck {
	one System
	some Feature
	some Story
	some TestCase
	some Input
	some Output 
	some Failure
	some Description
	some Resolution} 
run sanityCheck for 2 but 5 TestCase, 5 Feature

//instance where there is a story that has more than two test cases and more than two failures
pred anInstance[s:Story]{
	# s.testCases > 2
	#s.testCases.faults > 2
}run anInstance for 4 expect 1

//instance where there is a system with three features and atleast 3 stories have been written
pred anInstance2[sys: System]{
	#sys.allFeatures = 3
	#sys.allFeatures.stories > 2
}run anInstance2 for 4 expect 1
