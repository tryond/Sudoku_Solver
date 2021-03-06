# Submitter: tryond(tryon, daniel) 20621204
# Partner: joshuaek(klein, joshua) 58485794

# import copy
import variable
import domain
import copy

class Trail:
    def __init__(self):
        """
            Represents the trail of changes made. This allows backtracking to occur.
        """
        self.trailStack = []
        self.trailMarker = []

    ######### Accessors Method #########
    def size(self):
        return len(self.trailStack)

    ######### Modified Method #########
    def placeTrailMarker(self):
        """
            places a marker at the current point in the trail. Each time undo is
            called, the latest marker is popped and the trail
        """
        self.trailMarker.append(len(self.trailStack))
        # print("self.trailMarker: " + str(self.trailMarker))

    def push(self, v):
        """
            Adds a deep copy of a variable and its domain onto the trail.
        """
        # print("v in push--> " + str(v))
        domainCopy = copy.deepcopy(v.domain)
        vPair = [v, domainCopy] # v Variable and its deepcopy backup domain onto the trail
        self.trailStack.append(vPair)

        # print("======================= ")
        # print("self.trailStack at the moment: ")
        # for i in self.trailStack:
        #     print("variable --> " + str(i[0]))
        #     print("domain backup --> " + str(i[1]))
        # print("======================= ")

    def undo(self):
        """
            Pops changes pushed onto the trail until it reaches the latest marker.
            Also pops the latest marker.
        """
        targetSize = self.trailMarker.pop() # targetSize target position on the trail to backtrack to
        size = len(self.trailStack)
        while size > targetSize:
            vPair = self.trailStack.pop()
            v = vPair[0]
            v.setDomain(vPair[1])
            size -= 1

    def __str__(self):
        output = "trailStack: " + str(self.trailStack)
        output += "\ntrailMarker: " + str(self.trailMarker)
        return output

# Trail follows the singleton design pattern. A single class/object ever created.
masterTrailVariable = Trail()
