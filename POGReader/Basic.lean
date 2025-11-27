import POGReader.Parser
import POGReader.Extractor

namespace B.POG
  @[always_inline]
  def parseAndExtractGoals (path : System.FilePath) : IO (Array Goal) :=
    extractGoals <$> parse path
end B.POG
