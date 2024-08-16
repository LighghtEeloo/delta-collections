use super::*;
use ::serde::{Deserialize, Deserializer, Serialize, Serializer};

impl<K, V> Serialize for DeltaHashMap<K, V>
where
    K: Serialize,
    V: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let Self { base, delta } = self;
        serializer.serialize_newtype_struct("DeltaHashMap", &(base, delta))
    }
}

impl<'de, K, V> Deserialize<'de> for DeltaHashMap<K, V>
where
    K: Deserialize<'de> + Eq + Hash,
    V: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<DeltaHashMap<K, V>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (base, delta) = Deserialize::deserialize(deserializer)?;
        Ok(DeltaHashMap { base, delta })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde() {
        let mut map = DeltaHashMap::new();
        map.insert(1, 2);
        map.insert(3, 4);
        let json = serde_json::to_string(&map).unwrap();
        let map2: DeltaHashMap<i32, i32> = serde_json::from_str(&json).unwrap();
        assert_eq!(map, map2);
    }
}
