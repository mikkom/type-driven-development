module Shape

public export
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

private
rectangle_area : Double -> Double -> Double
rectangle_area width height = width * height

-- export
-- area : Shape -> Double
-- area (Triangle base height) = 0.5 * rectangle_area base height
-- area (Rectangle length height) = rectangle_area length height
-- area (Circle radius) = pi * radius * radius

export
data ShapeView : Shape -> Type where
     STriangle : ShapeView (Triangle base height)    
     SRectangle : ShapeView (Rectangle width height)    
     SCircle : ShapeView (Circle radius)    

total
export
shapeView : (shape : Shape) -> ShapeView shape
shapeView (Triangle x y) = STriangle
shapeView (Rectangle x y) = SRectangle
shapeView (Circle x) = SCircle

export
area : Shape -> Double
area shape with (shapeView shape)
  area (Triangle base height) | STriangle = 0.5 * base * height
  area (Rectangle width height) | SRectangle = width * height
  area (Circle radius) | SCircle = pi * radius * radius
