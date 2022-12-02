with Ada.Text_IO; use Ada.Text_IO;
with SPARK.Containers.Formal.Unbounded_Vectors; use SPARK.Containers.Formal;

procedure Day1
  with
    SPARK_Mode,
    Annotate => (GNATprove, Might_Not_Return)
is
   Max_Calories : constant := 100_000;
   Max_Items : constant := 500;
   Max_Elves : constant := 500;

   type Base_Calories is range 0 .. 3 * Max_Items * Max_Calories;
   subtype Sum_Calories is Base_Calories range 0 .. Max_Items * Max_Calories;
   subtype Calories is Sum_Calories range 1 .. Max_Calories;

   type Items is range 1 .. Max_Items;
   type Elves is range 1 .. Max_Elves;

   package Vect_Pos is new Unbounded_Vectors (Items, Calories);
   use Vect_Pos;
   package Vect_Calories is new Unbounded_Vectors (Elves, Vect_Pos.Vector);
   use Vect_Calories;
   Input : Vect_Calories.Vector;

   procedure Get_Input
     with Annotate => (GNATprove, Might_Not_Return)
   is
      File : Ada.Text_IO.File_Type;

      Line : String (1 .. 256);
      Last : Natural;
      Group : Vect_Pos.Vector;
   begin
      Open (File, In_File, "input");

      loop
         Get_Line (File, Line, Last);
         if Last = 0 then
            Input.Append (Group);
            Group.Clear;
         else
            Group.Append (Calories'Value (Line (Line'First .. Last)));
         end if;

         exit when End_Of_File (File);
      end loop;
   end Get_Input;

   type Sums_Array is array (Elves range 1 .. <>) of Sum_Calories
     with Predicate => Sums_Array'Last >= 3; --  Need at least 3 elves
   type Three_Elves is array (1 .. 3) of Elves;

   --  Return the index of the max value of Sums
   function Get_Max_Idx (Sums : Sums_Array) return Elves
   with
     Pre =>
       Sums'Length > 0,
     Post =>
       Get_Max_Idx'Result in Sums'Range and then
       (for all J in Sums'Range => Sums (J) <= Sums (Get_Max_Idx'Result))
   is
      Max_Idx : Elves range Sums'Range := 1;
   begin
      for S in Sums'Range loop
         if Sums (S) > Sums (Max_Idx) then
            Max_Idx := S;
         end if;

         pragma Loop_Invariant
           (for all J in Sums'First .. S => Sums (J) <= Sums (Max_Idx));
      end loop;

      return Max_Idx;
   end Get_Max_Idx;

   --  Return the indexes of the three max value of Sums
   function Get_Max_3 (Sums : Sums_Array) return Three_Elves
   with
     Pre =>
       Sums'Length >= 3,
     Post =>
       (declare
          Tops : constant Three_Elves := Get_Max_3'Result;
        begin
          (for all Top in Tops'Range => Tops (Top) in Sums'Range) and then
          Tops (1) /= Tops (2) and then
          Tops (1) /= Tops (3) and then
          Tops (2) /= Tops (3) and then
          (for all J in Sums'Range =>
             (if J not in Tops (1) | Tops (2) | Tops (3) then
                (for all Top in Tops'Range => Sums (J) <= Sums (Tops (Top))))))
   is
      Tops : Three_Elves with Relaxed_Initialization;
   begin
      --  Get the first 3 elves in decreasing order wrt their sum

      if Sums (1) >= Sum_Calories'Max (Sums (2), Sums (3)) then
         Tops (1) := 1;
         Tops (2) := (if Sums (2) >= Sums (3) then 2 else 3);
         Tops (3) := (if Sums (2) >= Sums (3) then 3 else 2);
      else
         Tops (1) := (if Sums (2) >= Sums (3) then 2 else 3);
         Tops (2) := (if Sums (1) >= Sums (5 - Tops (1)) then 1 else 5 - Tops (1));
         Tops (3) := (if Sums (1) >= Sums (5 - Tops (1)) then 5 - Tops (1) else 1);
      end if;

      pragma Assert (Sums (Tops (1)) >= Sums (Tops (2)));
      pragma Assert (Sums (Tops (2)) >= Sums (Tops (3)));

      --  Update Tops based on the rest of the elves

      for S in Sums'First + 3 .. Sums'Last loop
         if Sums (S) > Sums (Tops (1)) then
            Tops (3) := Tops (2);
            Tops (2) := Tops (1);
            Tops (1) := S;
         elsif Sums (S) > Sums (Tops (2)) then
            Tops (3) := Tops (2);
            Tops (2) := S;
         elsif Sums (S) > Sums (Tops (3)) then
            Tops (3) := S;
         end if;

         pragma Loop_Invariant (Tops'Initialized);
         pragma Loop_Invariant
           ((for all Top in Tops'Range => Tops (Top) in 1 .. S) and then
            Tops (1) /= Tops (2) and then
            Tops (1) /= Tops (3) and then
            Tops (2) /= Tops (3) and then
            Sums (Tops (2)) in Sums (Tops (3)) .. Sums (Tops (1)) and then
            (for all J in 1 .. S =>
              (if J not in Tops (1) | Tops (2) | Tops (3) then
                (for all Top in Tops'Range => Sums (J) <= Sums (Tops (Top))))));
      end loop;

      return Tops;
   end Get_Max_3;

begin
   --  Get all the input file into Input

   Get_Input;

   --  Get the sums over Input into Sums

   declare
      Num_Elves : constant Elves := Elves (Input.Length);
      Sums : Sums_Array (1 .. Num_Elves) := (others => 0);
   begin
      for G in Input.First_Index .. Input.Last_Index loop
         declare
            V : Vect_Pos.Vector renames Input.Element (G);
         begin
            for I in V.First_Index .. V.Last_Index loop
               Sums (G) := Sums (G) + V.Element (I);
               pragma Loop_Invariant (Sums (G) <= Sum_Calories (I) * Max_Calories);
            end loop;
         end;
      end loop;

      --  Puzzle 1

      declare
         Max : constant Sum_Calories := Sums (Get_Max_Idx (Sums));
      begin
         Put_Line (Max'Image);
      end;

      --  Puzzle 2

      declare
         Top_3 : constant Three_Elves := Get_Max_3 (Sums);
         Max_3 : constant Base_Calories :=
           Sums (Top_3 (1)) + Sums (Top_3 (2)) + Sums (Top_3 (3));
      begin
         Put_Line (Max_3'Image);
      end;
   end;
end day1;
