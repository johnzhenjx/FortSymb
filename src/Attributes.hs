module Attributes where

import Language.Fortran.AST

isAllocatable :: [Attribute a] -> Bool
isAllocatable attributes = any (\attr -> case attr of AttrAllocatable _ _ -> True; _ -> False) attributes

attributeDimensions :: [Attribute a] -> Maybe (AList DimensionDeclarator a)
attributeDimensions attributes =
    case attributes of
        [] -> Nothing
        attribute : remainingAttributes ->
            case attribute of
                AttrDimension _ann _span dimensionsInfo -> Just dimensionsInfo
                _ -> attributeDimensions remainingAttributes