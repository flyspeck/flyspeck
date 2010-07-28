-- file: process.hs

part :: (a -> Bool) -> [a] -> [[a]]

part _ [] = []
part test (x:[]) = if test x then []:[] else [x]:[]
part test (x:xs) = if test x then []:cont else (x:head cont):(tail cont)
    where 
       cont = part test xs

tocycles :: [Int] -> [[Int]]
tocycles [] = []
tocycles (len:rst) = (take len rst) : tocycles (drop len rst)

main = do
    -- Get the contents of stdin
    graphstrings <- getContents
    -- Partition with carriage returns
    let graphlines = part (=='\n') graphstrings
    -- Partition each line with spaces
    let graphlines2 = fmap (part (==' ')) graphlines
    -- Convert each string in the list of list strings to an int
    let graphlines3 = (fmap . fmap) (read::String->Int) graphlines2
    -- Drop the first two integers from the beginning of each list
    -- (Since these just represent the index and the number of nodes)
    let graphlines4 = fmap (drop 2) graphlines3
    -- turn each list of integers into cycle representation
    let graphlines5 = fmap tocycles graphlines4
    -- filter out empty lists, and lists containing empty lists
    let graphlines6 = filter (/=[[]]) $ filter (/=[]) graphlines5
    putStrLn (show graphlines6)
