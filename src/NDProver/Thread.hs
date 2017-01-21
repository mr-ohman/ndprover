
module NDProver.Thread where

import Control.Concurrent

forkRace :: a -> b -> IO (Either a b)
forkRace a b = do
    res <- newEmptyMVar
    ta <- forkIO (process a Left res)
    tb <- forkIO (process b Right res)
    result <- takeMVar res
    killThread ta
    killThread tb
    return result

-- First interesting when True, other interesting when False
forkInterest :: (Bool, a) -> (Bool, b) -> IO (Either a b)
forkInterest a b = do
    resA <- newEmptyMVar
    resB <- newEmptyMVar
    resFinal <- newEmptyMVar
    ta <- forkIO (processB a Left resA resFinal)
    tb <- forkIO (processB b Right resB resFinal)
    interest <- takeMVar resFinal
    if interest
        then do result <- takeMVar resB
                killAndReturn ta tb result
        else do result <- takeMVar resA
                killAndReturn ta tb result
  where killAndReturn ta tb res = do
            killThread ta
            killThread tb
            return res

process :: t -> (t -> a) -> MVar a -> IO ()
process a dir res = a `seq` putMVar res (dir a)

processB :: (b, t) -> (t -> a) -> MVar a -> MVar b -> IO ()
processB a dir res resF = a `seq` do
    let (b, r) = a
    putMVar res (dir r)
    putMVar resF b
