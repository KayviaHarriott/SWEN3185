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


sig BugTracking{
	allFeatures: set Feature,
	reliabilityStat: lone ReliabilityStatus,

	allStories: set Story,
	allTestCases: set TestCase,
	allFailures: set Failure,
	
	fStories: allFeatures->allStories,
	storyOrder: allStories -> allStories,
	tc: allFeatures -> allStories -> allTestCases
}

--- PREDICATES

pred inv[bt: BugTracking]{ 
	all s: bt.allStories| some f: bt.allFeatures| s in fStories
}

fact noLooseStory{
	all story: Story | some feat: Feature| story in feat.stories
}


--- FACTS

fact { all bt: BugTracking| inv[bt] }


-- INSTANCES

//Instance of all relations in the model
//pred sanityCheck {
//	one System
//	#Feature = 2
//	#Story  = 3
//	#TestCase = 3
//	#Input = 2
//	#Output = 2
//	#Failure > 3
//	some failure: Failure | failure.state = Unresolved
//	some Description
//	some Resolution} 
//run sanityCheck for 6 but 1 System

pred sanityCheck{
	some bt: BugTracking{
		some Feature.(bt.fStories)
	}
} run sanityCheck for 6 but 1 BugTracking expect 1


-- FUNCTIONS

/* returns Pre(v) for vertex v in graph g */
fun pre[g: Story->Story, v: Story]: set Story {g.v}
run pre for 6

/* returns Post(v) for vertex v in graph g */
fun post[g: Story->Story, v: Story]: set Story {v.g}
run post for 6

